#!/usr/bin/env node
/*  Cloud paper-bot — ONE catch-up cycle, then exits (for GitHub Actions cron).
 *  Each run: replays 1-minute candles since the open trade to catch any take-profit
 *  or liquidation exactly, then evaluates the current signal for a new entry.
 *  State persists in state.json (committed back by the workflow). No keys, no money.
 */
const fs = require("fs");
const path = require("path");

const CFG = { targetProfitPct: 70, feePerSide: 0.02, margin: 50, leverage: 100 };
const NOT = CFG.margin * CFG.leverage;
const LIQ = 0.0086;
const STATE = path.join(__dirname, "state.json");

// ---- feeds (live futures, Binance → Bybit) ----
const KSRC = [
  { url:i=>`https://fapi.binance.com/fapi/v1/klines?symbol=BTCUSDT&interval=${i}&limit=1000`,
    parse:d=>d.map(k=>({t:+k[0],o:+k[1],h:+k[2],l:+k[3],c:+k[4],v:+k[5]})) },
  { url:i=>`https://api.bybit.com/v5/market/kline?category=linear&symbol=BTCUSDT&interval=${i==="5m"?"5":i==="15m"?"15":"1"}&limit=1000`,
    parse:d=>d.result.list.map(k=>({t:+k[0],o:+k[1],h:+k[2],l:+k[3],c:+k[4],v:+k[5]})).reverse() },
];
const PXSRC = [
  { u:"https://fapi.binance.com/fapi/v1/ticker/price?symbol=BTCUSDT", g:j=>+j.price },
  { u:"https://api.bybit.com/v5/market/tickers?category=linear&symbol=BTCUSDT", g:j=>+j.result.list[0].lastPrice },
];
async function fetchT(url, ms=12000){ const ac=new AbortController(); const id=setTimeout(()=>ac.abort(),ms);
  try{ const r=await fetch(url,{signal:ac.signal}); return r.ok?await r.json():null; }catch(e){ return null; }finally{ clearTimeout(id); } }
async function getK(i){ for(const s of KSRC){ const j=await fetchT(s.url(i)); if(j){ try{const r=s.parse(j); if(r&&r.length>60) return r;}catch(e){} } } return null; }
async function getPx(){ for(const s of PXSRC){ const j=await fetchT(s.u); if(j){ try{const v=s.g(j); if(v) return v;}catch(e){} } } return null; }

// ---- indicators ----
function ema(v,p){ const k=2/(p+1); const o=[]; let e=v.slice(0,p).reduce((a,b)=>a+b,0)/p;
  for(let i=0;i<v.length;i++){ if(i<p){o.push(null);continue;} e=v[i]*k+e*(1-k); o.push(e);} o[p-1]=v.slice(0,p).reduce((a,b)=>a+b,0)/p; return o; }
function rsi(v,p=14){ let g=0,l=0; for(let i=1;i<=p;i++){const d=v[i]-v[i-1]; d>=0?g+=d:l-=d;} g/=p;l/=p;
  const o=new Array(p).fill(null); o.push(100-100/(1+g/(l||1e-9)));
  for(let i=p+1;i<v.length;i++){const d=v[i]-v[i-1],ug=d>0?d:0,ul=d<0?-d:0; g=(g*(p-1)+ug)/p; l=(l*(p-1)+ul)/p; o.push(100-100/(1+g/(l||1e-9)));} return o; }
function atr(r,p=14){ const tr=[]; for(let i=1;i<r.length;i++){const h=r[i].h,lo=r[i].l,pc=r[i-1].c; tr.push(Math.max(h-lo,Math.abs(h-pc),Math.abs(lo-pc)));}
  let a=tr.slice(0,p).reduce((x,y)=>x+y,0)/p; for(let i=p;i<tr.length;i++)a=(a*(p-1)+tr[i])/p; return a; }
function vwap(r){ const n=new Date(); const mid=Date.UTC(n.getUTCFullYear(),n.getUTCMonth(),n.getUTCDate());
  let pv=0,vv=0,u=0; for(const x of r){ if(x.t>=mid){const tp=(x.h+x.l+x.c)/3; pv+=tp*x.v; vv+=x.v; u++;}}
  if(u<2){ const t=r.slice(-48); pv=0;vv=0; for(const x of t){const tp=(x.h+x.l+x.c)/3; pv+=tp*x.v; vv+=x.v;}} return vv?pv/vv:null; }

// ---- signal (gates only; flow is a bonus and not needed for the decision) ----
async function computeSignal(){
  const five=await getK("5m"); if(!five) return {ok:false};
  const fifteen=await getK("15m");
  const price=(await getPx()) || five.at(-1).c;
  const rowsC=five.slice(0,-1); const c=rowsC.map(x=>x.c); const dec=rowsC.at(-1);
  const e9=ema(c,9).at(-1), e21=ema(c,21).at(-1), e50=ema(c,50).at(-1);
  const vw=vwap(rowsC); const rsiNow=rsi(c,14).at(-1);
  const vols=rowsC.map(x=>x.v), avgVol=vols.slice(-21,-1).reduce((a,b)=>a+b,0)/20;
  const volDead=avgVol?vols.at(-1)/avgVol<0.6:false;
  let mtfUp=false,mtfDown=false;
  if(fifteen){ const c15=fifteen.slice(0,-1).map(x=>x.c); const p15=c15.at(-1); const E9=ema(c15,9).at(-1),E50=ema(c15,50).at(-1);
    mtfUp=p15>E50&&E9>E50; mtfDown=p15<E50&&E9<E50; }
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
  return {ok:true, price, dir, actionable:gPass&&dir!=null, tp, liq, win, rsi:rsiNow,
          gatesPassed:gates.filter(Boolean).length, gatesTotal:gates.length||5};
}

const f=n=>n==null?"—":n.toLocaleString("en-US",{maximumFractionDigits:1});

(async ()=>{
  let st={ open:null, history:[], wasActionable:false };
  try{ st=Object.assign(st, JSON.parse(fs.readFileSync(STATE,"utf8"))); }catch(e){}
  let changed=false;

  // 1) replay 1m candles to resolve an open trade exactly (TP or liquidation)
  if(st.open){
    const o=st.open; const one=await getK("1m");
    if(one){
      for(const k of one.filter(x=>x.t>=o.t).sort((a,b)=>a.t-b.t)){
        let hit=null, px=null;
        if(o.dir==="long"){ if(k.l<=o.liq){hit="LOSS";px=o.liq;} else if(k.h>=o.tp){hit="WIN";px=o.tp;} }
        else { if(k.h>=o.liq){hit="LOSS";px=o.liq;} else if(k.l<=o.tp){hit="WIN";px=o.tp;} }
        if(hit){ const pnl=hit==="WIN"?o.win:-CFG.margin;
          st.history.push({dir:o.dir,entry:o.entry,exit:px,pnl,hit,t:k.t});
          console.log(`${hit==="WIN"?"✅":"💀"} CLOSE ${o.dir.toUpperCase()} @ ${f(px)} → ${pnl>=0?"+":""}$${pnl.toFixed(2)} (${hit})`);
          st.open=null; changed=true; break; }
      }
    }
  }

  // 2) evaluate current signal for a fresh entry (only when flat)
  const sig=await computeSignal();
  if(sig.ok){
    if(!st.open && sig.actionable && !st.wasActionable && sig.dir){
      st.open={dir:sig.dir, entry:sig.price, tp:sig.tp, liq:sig.liq, win:sig.win, t:Date.now()};
      console.log(`🟢 OPEN ${sig.dir.toUpperCase()} @ ${f(sig.price)} · TP ${f(sig.tp)} (+$${sig.win.toFixed(2)}) · liq ${f(sig.liq)}`);
      changed=true;
    }
    const newWas=sig.actionable;
    if(newWas!==st.wasActionable){ st.wasActionable=newWas; changed=true; }
    const tag=st.open?`IN ${st.open.dir.toUpperCase()}`:(sig.actionable?`⚡ ${sig.dir.toUpperCase()} SIGNAL`:`wait (${sig.gatesPassed}/${sig.gatesTotal})`);
    console.log(`${f(sig.price)} · ${tag} · RSI ${sig.rsi?.toFixed(0)}`);
  } else { console.log("(no data this run)"); }

  // 3) save + scorecard
  if(changed) fs.writeFileSync(STATE, JSON.stringify(st,null,2));
  const h=st.history, n=h.length, w=h.filter(x=>x.pnl>0).length, net=h.reduce((a,x)=>a+x.pnl,0);
  console.log(`📒 trades ${n} · win-rate ${n?(w/n*100).toFixed(0):0}% (${w}/${n}) · net $${net.toFixed(2)}`);
})();
