"use strict";

const {INPUT,verify,assert}=require("./issue163_fourier_caps.cjs");
const {loadField,verifyField,group,SIGMA,ENDPOINT_FILE}=require("./issue163_reweighted_field.cjs");
const {lift}=require("./issue163_dyadic_lift.cjs");

const SLOPES=[1000,0,500,500,500,500,1000,1000,1000,1000,1000,1000,1000,1000];

function replayCombined(raw,io){
  const {states,child}=loadField(raw,io),trace=Array(child.count);
  const leaves=new Map(states.filter(st=>st.n<112).map(st=>[st.n,{trace:Array(st.count),repairs:new Map()}]));
  const parent=verifyField(states,child.area,trace,(st,p,cost,d)=>{
    const row=leaves.get(st.n);row.trace[p]=cost;if(d)row.repairs.set(p,d);
  });
  const budget=BigInt(parent.global_trace_numerator),denominator=BigInt(parent.trace_denominator);
  const next=lift(child.boxes,trace,budget,child.area);
  const field={
    budget,denominator,factor:BigInt(next.pi_squared_factor_floor_1e18),
    trace:(st,p)=>leaves.get(st.n).trace[p],
    matrix(st,p){
      const n=st.n,row=leaves.get(n),d=row.repairs.get(p);
      const scales=Array.from(st.boxes.subarray(n*p,n*(p+1)),j=>BigInt(SIGMA[group((st.grid[j]+st.grid[j+1])/2)]));
      const diagonal=scales.map((s,i)=>2n*BigInt(d?d[i]:st.diagonal[n*p+i])*s*s);
      assert(diagonal.reduce((a,b)=>a+b,0n)===row.trace[p],"weighted coarse witness trace");
      return {denominator,slack:budget-row.trace[p],diagonal,
        edge:(i,j)=>2n*BigInt(st.edge(p,i,j))*scales[i]*scales[j]};
    }
  };
  const annulus=verify(states.filter(st=>st.n<112),SLOPES,field);
  assert(BigInt(annulus.pi_squared_factor_floor_1e18)>=617166391098385050n,"combined lower bound");
  assert(BigInt(annulus.fixed_shell_rule_upper_1e12)<=6091188129791n,"fixed shell rule ceiling");
  return {finite:next,annulus};
}
if(typeof module!=="undefined" && require.main===module){
  const fs=require("node:fs"),path=require("node:path"),zlib=require("node:zlib"),crypto=require("node:crypto");
  const dir=process.argv[2];if(!dir)throw Error("Pass the finite certificate directory.");
  const raw={endpoints:fs.readFileSync(path.join(dir,ENDPOINT_FILE))};
  for(const [key,[file]]of Object.entries(INPUT))raw[key]=fs.readFileSync(path.join(dir,file));
  const io={hash:data=>crypto.createHash("sha256").update(data).digest("hex"),utf8:data=>data.toString("utf8"),
    ungzip:zlib.gunzipSync,inflate:zlib.inflateRawSync};
  console.log(JSON.stringify(replayCombined(raw,io),null,2));
}
