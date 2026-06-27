#!/usr/bin/env node
/*  Cloud paper-bot — BAR-BY-BAR, no-gap version (for GitHub Actions cron).
 *  Each run processes EVERY 5-minute candle that has closed since the last run,
 *  so no entry is missed during the 15-minute sleep. For each new closed candle it:
 *    1) resolves any open trade: liquidation → profit-lock → take-profit,
 *    2) opens a fresh trade only when the signal fires AND volume is firing (≥1.3x avg).
 *  Backtested edges baked in (vs base signal, which loses): the volume-firing entry
 *  filter turns 30-day net positive even with fees; the profit-lock (arm +45% → stop +10%)
 *  banks near-miss winners instead of letting them round-trip to liquidation.
 *  Indicators are recomputed as-of each candle's close (no look-ahead).
 *  State persists in state.json (committed back by the workflow). No keys, no money.
 */
const fs = require("fs");
const path = require("path");

const CFG = { targetProfitPct: 70, feePerSide: 0.02, margin: 50, leverage: 100 };
const NOT = CFG.margin * CFG.leverage;
const rtFee = 2 * NOT * (CFG.feePerSide / 100);   // round-trip fee in $
const LIQ = 0.0086;
// edge config (backtested winners): only enter on firing volume; bank near-miss winners with a profit-lock
const VOL_FIRING = 1.3;   // entry needs volume ≥ this × the 20-bar average
const ARM_PCT = 45;       // once profit peaks at +45% of margin…
const LOCK_PCT = 10;      // …a stop locks in +10% (instead of letting it round-trip to liquidation)
const FIVE_MS = 5 * 60000, FIFTEEN_MS = 15 * 60000;
const STATE = path.join(__dirname, "state.json");

// ---- feeds (live futures, Binance → Bybit) ----
const KSRC = [
  { url:i=>`https://fapi.binance.com/fapi/v1/klines?symbol=BTCUSDT&interval=${i}&limit=1000`,
    parse:d=>d.map(k=>({t:+k[0],o:+k[1],h:+k[2],l:+k[3],c:+k[4],v:+k[5]})) },
  { url:i=>`https://api.bybit.com/v5/market/kline?category=linear&symbol=BTCUSDT&interval=${i==="5m"?"5":i==="15m"?"15":"1"}&limit=1000`,
    parse:d=>d.result.list.map(k=>({t:+k[0],o:+k[1],h:+k[2],l:+k[3],c:+k[4],v:+k[5]})).reverse() },
];
async function fetchT(url, ms=12000){ const ac=new AbortController(); const id=setTimeout(()=>ac.abort(),ms);
  try{ const r=await fetch(url,{signal:ac.signal}); return r.ok?await r.json():null; }catch(e){ return null; }finally{ clearTimeout(id); } }
async function getK(i){ for(const s of KSRC){ const j=await fetchT(s.url(i)); if(j){ try{const r=s.parse(j); if(r&&r.length>60) return r;}catch(e){} } } return null; }

// ---- indicators ----
function ema(v,p){ const k=2/(p+1); const o=[]; let e=v.slice(0,p).reduce((a,b)=>a+b,0)/p;
  for(let i=0;i<v.length;i++){ if(i<p){o.push(null);continue;} e=v[i]*k+e*(1-k); o.push(e);} o[p-1]=v.slice(0,p).reduce((a,b)=>a+b,0)/p; return o; }
function rsi(v,p=14){ let g=0,l=0; for(let i=1;i<=p;i++){const d=v[i]-v[i-1]; d>=0?g+=d:l-=d;} g/=p;l/=p;
  const o=new Array(p).fill(null); o.push(100-100/(1+g/(l||1e-9)));
  for(let i=p+1;i<v.length;i++){const d=v[i]-v[i-1],ug=d>0?d:0,ul=d<0?-d:0; g=(g*(p-1)+ug)/p; l=(l*(p-1)+ul)/p; o.push(100-100/(1+g/(l||1e-9)));} return o; }
// session VWAP anchored to the UTC day of `asOfMs`, summing candles up to that time
function vwapAsOf(rows, asOfMs){ const d=new Date(asOfMs); const mid=Date.UTC(d.getUTCFullYear(),d.getUTCMonth(),d.getUTCDate());
  let pv=0,vv=0,u=0; for(const x of rows){ if(x.t>=mid && x.t<=asOfMs){const tp=(x.h+x.l+x.c)/3; pv+=tp*x.v; vv+=x.v; u++;}}
  if(u<2){ const t=rows.slice(-48); pv=0;vv=0; for(const x of t){const tp=(x.h+x.l+x.c)/3; pv+=tp*x.v; vv+=x.v;}} return vv?pv/vv:null; }

// ---- signal AS-OF a closed 5m candle (index i in `closed`) ----
// `closed` = closed 5m candles (forming one already removed). `f15` = all 15m candles.
function signalAt(closed, f15, i){
  const rowsC = closed.slice(0, i+1);
  if(rowsC.length < 60) return null;
  const dec = rowsC[rowsC.length-1];                 // decision candle
  const closeMs = dec.t + FIVE_MS - 1;               // its close timestamp
  const c = rowsC.map(x=>x.c);
  const e9=ema(c,9).at(-1), e21=ema(c,21).at(-1), e50=ema(c,50).at(-1);
  const vw=vwapAsOf(rowsC, closeMs); const rsiNow=rsi(c,14).at(-1);
  const vols=rowsC.map(x=>x.v), avgVol=vols.slice(-21,-1).reduce((a,b)=>a+b,0)/20;
  const volRatio=avgVol?vols.at(-1)/avgVol:0; const volDead=volRatio<0.6;
  // 15m trend using only 15m candles fully closed by this moment
  let mtfUp=false,mtfDown=false;
  if(f15){ const c15arr=f15.filter(x=>x.t+FIFTEEN_MS<=closeMs).map(x=>x.c);
    if(c15arr.length>50){ const p15=c15arr.at(-1); const E9=ema(c15arr,9).at(-1),E50=ema(c15arr,50).at(-1);
      mtfUp=p15>E50&&E9>E50; mtfDown=p15<E50&&E9<E50; } }
  const price=dec.c;
  const aboveVwap=vw!=null&&dec.c>vw, belowVwap=vw!=null&&dec.c<vw;
  const hi=Math.max(e9,e21,e50),lo=Math.min(e9,e21,e50),spreadPct=(hi-lo)/price*100;
  const bunched=spreadPct<0.05;
  const fanUp=e9>e21&&e21>e50&&!bunched, fanDown=e9<e21&&e21<e50&&!bunched;
  const distPct=(dec.c-e9)/dec.c*100;
  const nearLines=Math.abs(distPct)<0.06||(dec.c>=Math.min(e9,e21)&&dec.c<=Math.max(e9,e21));
  const extUp=distPct>0.12, extDn=distPct<-0.12;
  let cand=bunched?"none":fanUp?"long":fanDown?"short":"none";
  let gates=[];
  if(cand==="long") gates=[mtfUp,aboveVwap,nearLines&&!extUp,rsiNow<68,!volDead];
  else if(cand==="short") gates=[mtfDown,belowVwap,nearLines&&!extDn,rsiNow>32,!volDead];
  const gPass=gates.length&&gates.every(Boolean);
  const dir=(cand==="long"||cand==="short")?cand:null;
  const tgt=CFG.targetProfitPct/100, movePct=tgt/CFG.leverage, sign=cand==="short"?-1:1;
  const tp=price*(1+sign*movePct), liq=price*(1-sign*LIQ);
  const win=tgt*CFG.margin - 2*NOT*(CFG.feePerSide/100);
  return { dir, entry:price, tp, liq, win, t:dec.t, rsi:rsiNow, volRatio, firing:volRatio>=VOL_FIRING,
           actionable:gPass&&dir!=null, gatesPassed:gates.filter(Boolean).length, gatesTotal:gates.length||5 };
}

const f=n=>n==null?"—":n.toLocaleString("en-US",{maximumFractionDigits:1});

(async ()=>{
  let st={ open:null, history:[], wasActionable:false, lastBar:0 };
  try{ st=Object.assign(st, JSON.parse(fs.readFileSync(STATE,"utf8"))); }catch(e){}

  const five=await getK("5m"); const f15=await getK("15m");
  if(!five){ console.log("(no data this run)");
    const h=st.history; console.log(`📒 trades ${h.length} · win-rate ${h.length?(h.filter(x=>x.pnl>0).length/h.length*100).toFixed(0):0}% · net $${h.reduce((a,x)=>a+x.pnl,0).toFixed(2)}`); return; }

  const closed = five.slice(0,-1);                   // drop the still-forming candle
  let changed=false;

  // First-ever run: prime to the latest closed bar, take no backfill trades.
  if(!st.lastBar){
    const last=closed[closed.length-1];
    const s=signalAt(closed, f15, closed.length-1);
    st.lastBar=last.t; st.wasActionable = s ? (s.actionable && s.firing && !!s.dir) : false;
    fs.writeFileSync(STATE, JSON.stringify(st,null,2));
    console.log(`primed @ ${f(last.c)} · ${st.wasActionable?"signal armed":"wait"} · watching from here`);
    console.log(`📒 trades 0 · win-rate 0% · net $0.00`);
    return;
  }

  // Walk every newly-closed 5m candle in order.
  let opened=0, closedN=0;
  for(let i=0;i<closed.length;i++){
    const bar=closed[i];
    if(bar.t<=st.lastBar) continue;
    // 1) resolve an open trade on this bar (liquidation → profit-lock → target).
    //    Profit-lock: once peak profit reaches +ARM%, a stop sits at +LOCK% (banks near-miss winners).
    if(st.open){
      const o=st.open; const sgn=o.dir==="long"?1:-1;
      const armPx  = o.entry*(1+sgn*(ARM_PCT/100/CFG.leverage));
      const lockPx = o.entry*(1+sgn*(LOCK_PCT/100/CFG.leverage));
      let hit=null,px=null;
      if(o.dir==="long"){
        if(bar.l<=o.liq){hit="LOSS";px=o.liq;}
        else if(o.armed && bar.l<=lockPx){hit="LOCK";px=lockPx;}
        else if(bar.h>=o.tp){hit="WIN";px=o.tp;}
      } else {
        if(bar.h>=o.liq){hit="LOSS";px=o.liq;}
        else if(o.armed && bar.h>=lockPx){hit="LOCK";px=lockPx;}
        else if(bar.l<=o.tp){hit="WIN";px=o.tp;}
      }
      if(hit){ const pnl = hit==="LOSS" ? -CFG.margin : hit==="LOCK" ? (LOCK_PCT/100*CFG.margin - rtFee) : o.win;
        st.history.push({dir:o.dir,entry:o.entry,exit:px,pnl,hit,t:bar.t});
        console.log(`${hit==="WIN"?"✅":hit==="LOCK"?"🔒":"💀"} CLOSE ${o.dir.toUpperCase()} @ ${f(px)} → ${pnl>=0?"+":""}$${pnl.toFixed(2)} (${hit})`);
        st.open=null; closedN++;
      } else { // not closed → ratchet the peak and arm the lock once it reaches +ARM%
        if(o.dir==="long"){ if(bar.h>o.peak)o.peak=bar.h; if(o.peak>=armPx)o.armed=true; }
        else { if(bar.l<o.peak)o.peak=bar.l; if(o.peak<=armPx)o.armed=true; }
      }
    }
    // 2) fresh entry on this closed bar — needs the signal AND volume firing (the edge filter)
    const s=signalAt(closed, f15, i);
    if(s){
      const fire = s.actionable && s.firing && !!s.dir;
      if(!st.open && fire && !st.wasActionable){
        st.open={dir:s.dir, entry:s.entry, tp:s.tp, liq:s.liq, win:s.win, t:s.t, peak:s.entry, armed:false};
        console.log(`🟢 OPEN ${s.dir.toUpperCase()} @ ${f(s.entry)} · TP ${f(s.tp)} (+$${s.win.toFixed(2)}) · liq ${f(s.liq)} · vol ${s.volRatio.toFixed(1)}x`);
        opened++;
      }
      st.wasActionable = fire;
    }
    st.lastBar=bar.t; changed=true;
  }

  // status line (latest closed bar)
  const last=signalAt(closed, f15, closed.length-1);
  if(last){
    const fire=last.actionable&&last.firing&&last.dir;
    const tag=st.open?`IN ${st.open.dir.toUpperCase()}${st.open.armed?" 🔒":""}`
      :(fire?`⚡ ${last.dir.toUpperCase()} SIGNAL`:last.actionable&&!last.firing?`wait (vol ${last.volRatio.toFixed(1)}x, need ${VOL_FIRING}x)`:`wait (${last.gatesPassed}/${last.gatesTotal})`);
    console.log(`${f(last.entry)} · ${tag} · RSI ${last.rsi?.toFixed(0)} · processed ${opened} new entr${opened===1?"y":"ies"}, ${closedN} close${closedN===1?"":"s"} this run`);
  }

  if(changed) fs.writeFileSync(STATE, JSON.stringify(st,null,2));
  const h=st.history, n=h.length, w=h.filter(x=>x.pnl>0).length, net=h.reduce((a,x)=>a+x.pnl,0);
  console.log(`📒 trades ${n} · win-rate ${n?(w/n*100).toFixed(0):0}% (${w}/${n}) · net $${net.toFixed(2)}`);
})();
