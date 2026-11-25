"use strict";

const {INPUT,assert,piInterval}=require("./issue163_fourier_caps.cjs");
const {loadField,verifyField,canonicalParent,ENDPOINT_FILE}=require("./issue163_reweighted_field.cjs");
const N=224;
const NEW=[[1,0,0],[1,0,1],[2,1,2]];
function orbit(rep){
  const seen=new Map(),stack=[rep];
  while(stack.length){
    const [k,x,y]=stack.pop(),id=(k*N+x)*N+y;if(seen.has(id))continue;
    seen.set(id,[k,x,y]);stack.push([k,y,x],[k,N-1-x,N-1-y],[N-k,y,N-1-x]);
  }
  return Array.from(seen.values());
}
function orbitData(rep){
  const terms=[];let weight=0;
  for(const [k,x,y] of orbit(rep)){
    const a=Math.abs(x-y),b=Math.abs(x+y-N+1);assert(a<=k && b<=N-k,"boundary polygon geometry");
    weight+=(N-k)*(a===k||b===N-k?1:2);
    // Each label has the form index + offset, with offset between -2 and 1.
    for(let i=Math.max(0,x-1,y-k-1);i<=Math.min(N-1-k,x+2,y-k+2);i++){
      terms.push([i,i+k,x-i,y-i-k]);
    }
  }
  return {terms,weight}; // weight is in units of 1 / (2 N^2) for action / pi^2.
}
function offset(type,i,a,ab,abc){
  if(type===0)return i<a?0:-1;
  return i<a?1:i<ab?0:i<abc?-1:-2;
}
function count(terms,type,a,ab,abc){
  let n=0;for(const [i,j,x,y] of terms){
    if(offset(type,i,a,ab,abc)===x && offset(type,j,a,ab,abc)===y)n++;
  }
  return n;
}
function frozenUpper(){
  const orbits=new Map();
  for(let k=1;k<=N/2;k++)for(let x=0;x<2;x++)for(let y=0;y<N;y++){
    if(Math.abs(x-y)>k || Math.abs(x+y-N+1)>N-k)continue;
    const r=orbit([k,x,y]).sort((a,b)=>a[0]-b[0]||a[1]-b[1]||a[2]-b[2])[0];
    orbits.set(r.join(","),r);
  }
  assert(orbits.size===666,"fresh endpoint classes");
  for(const r of orbits.values()){
    const {terms,weight}=orbitData(r);
    const ca=count(terms,0,1,1,1),cb=count(terms,1,1,2,3);
    assert(2*N*(ca+2*cb)>=weight,"two-profile dual coverage");
  }
}
function lift(boxes,trace,U,action){
  frozenUpper();
  const parentIndex=new Map(),n=N/2;
  for(let i=0;i<trace.length;i++){
    parentIndex.set(String.fromCharCode(...boxes.subarray(n*i,n*(i+1))),i);
  }
  const lookup=new Int32Array((n+1)**2).fill(-1);
  function parent(u,v){
    const key=(n+1)*u+v;if(lookup[key]>=0)return lookup[key];
    const row=Uint8Array.from({length:n},(_,i)=>i+Number(i<u)-Number(i>=v));
    const [canonical]=canonicalParent(row),id=parentIndex.get(canonical);
    assert(id!==undefined,"canonical 112-point parent");lookup[key]=id;return id;
  }
  assert(parent(0,1)===0 && parent(0,112)===0,"both dual rows project to parent zero");
  const cls=NEW.map(orbitData),q=[2,1,2];
  assert(cls.reduce((v,o,j)=>v+q[j]*o.weight,0)===24*N,"three-orbit action");
  const maxLoad=BigInt(cls.reduce((v,o,j)=>v+q[j]*o.terms.length,0));
  const slack=U-trace[0];assert(slack>=0n,"parent budget");
  let ln=slack,ld=1n,rows=0;
  function inspect(t,a,b,c,i,j){
    rows++;
    const avail=2n*(2n*U-trace[i]-trace[j]);assert(avail>=0n,"inherited trace");
    if(avail*ld>=ln*maxLoad)return;
    const g=BigInt(cls.reduce((v,o,k)=>v+q[k]*count(o.terms,t,a,a+b,a+b+c),0));
    if(g>0n && avail*ld<ln*g){ln=avail;ld=g;}
  }
  for(let a=1;a<=N;a++)inspect(0,a,0,0,parent(0,Math.ceil(a/2)),parent(0,n));
  for(let a=1;a<N;a++)for(let b=0;b<=N-a;b++)for(let c=0;c<=N-a-b;c++){
    if(a+b+c<N && !b && !c)continue;
    inspect(1,a,b,c,parent(0,Math.ceil((a+b)/2)),parent(Math.floor(a/2),Math.floor((a+b+c)/2)));
  }
  assert(rows===1898400,"complete rooted 224 endpoint enumeration");
  const n2=112n**2n,unit=10n**18n;
  const num=2n*action*224n*ld+3n*ln*n2,den=n2*224n*ld*U;
  const factor=num*unit/den,pi=piInterval()[0];
  return {rooted_profiles:rows,distinct_parent_lookups:lookup.reduce((a,v)=>a+Number(v>=0),0),dual_classes:666,
    parent_zero_trace:String(trace[0]),raw_budget:String(U),increment_numerator:String(ln),
    increment_denominator:String(ld),dual_slack_numerator:String(slack),attains_frozen_upper:ln===ld*slack,
    pi_squared_factor_floor_1e18:String(factor),area_floor_1e18:String(factor*pi*pi/(10n**96n))};
}
function replayLift(raw,io){
  const {states,child}=loadField(raw,io),trace=Array(child.count);
  const result=verifyField(states,child.area,trace);
  const out=lift(child.boxes,trace,BigInt(result.global_trace_numerator),child.area);
  assert(BigInt(out.pi_squared_factor_floor_1e18)>=617154280862042281n,"certified lifted coefficient");
  return {parent:result,lift:out};
}
if(typeof module!=="undefined" && require.main===module){
  const fs=require("node:fs"),path=require("node:path"),zlib=require("node:zlib"),crypto=require("node:crypto");
  const dir=process.argv[2];if(!dir)throw Error("Pass the finite certificate directory.");
  const raw={endpoints:fs.readFileSync(path.join(dir,ENDPOINT_FILE))};
  for(const [key,[file]]of Object.entries(INPUT))raw[key]=fs.readFileSync(path.join(dir,file));
  const io={hash:data=>crypto.createHash("sha256").update(data).digest("hex"),utf8:data=>data.toString("utf8"),
    ungzip:zlib.gunzipSync,inflate:zlib.inflateRawSync};
  console.log(JSON.stringify(replayLift(raw,io),null,2));
}
