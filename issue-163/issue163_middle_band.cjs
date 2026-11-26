"use strict";

const path = require("node:path");
const zlib = require("node:zlib");
const {INPUT, npzReader, piInterval, assert} = require("./issue163_fourier_caps.cjs");
const {makeLevel, readCorrection} = require("./issue163_free_field.cjs");
const {pinned, HERM_DEN, BASE_NUM, BASE_DEN} = require("./issue163_midpoint.cjs");
const {cosPi, S} = require("./issue163_hemisphere_cap.cjs");

const n=112, N=BigInt(n), unit=10n**12n, fieldDen=HERM_DEN/2n;
const dir=process.argv[2] || path.join(__dirname,"issue163_inputs");
const archive=name=>npzReader(pinned(dir,...INPUT[name]),zlib.inflateRawSync);
const maps=archive("maps"), base=archive("field")("master_numerators");
const correction="issue163_free_coefficients.json";
pinned(__dirname,correction,"254eee5682f2dbd27510523684e67e3e2d88ea14344ba2836fe1be155041beea");
const {delta,cap}=readCorrection(path.join(__dirname,correction),base.length);
const grid=Array.from({length:n+1},(_,i)=>i-n/2);
const level=makeLevel({n,grid,boxes:[]},maps,base,delta,null);
const scalar=Array.from(level.scalar,BigInt);
const fieldScale=fieldDen*cap;
assert(level.action*unit*BASE_DEN===2n*N*N*fieldScale*BASE_NUM,"free area and normalization");
function entry(k,a,b) {
  const id=level.index[level.key(k,a,b)];
  return id<0?0n:level.w[id]*scalar[a]*scalar[b];
}

const digits=10n**12n, piUnit=10n**48n, [piLo,piHi]=piInterval();
const floorDiv=(a,b)=>a/b-(a%b<0n?1n:0n);
const ceilDiv=(a,b)=>-floorDiv(-a,b);
const format=v=>(v/digits)+"."+(v%digits).toString().padStart(12,"0");
function piSquared(num,den,upper) {
  assert(num>0n && den>0n,"positive multiple of pi squared");
  return upper?ceilDiv(num*piHi**2n*digits,den*piUnit**2n):
    floorDiv(num*piLo**2n*digits,den*piUnit**2n);
}

// Twice a rectangle's area above x+y=t, in integer third-bin coordinates.
const posSq=x=>Math.max(x,0)**2;
function corner2(a,b,c,d,t) {
  return posSq(b+d-t)-posSq(a+d-t)-posSq(b+c-t)+posSq(a+c-t);
}
function outerFlux() {
  let total=0n;
  for (let k=1;k<n;++k) for (let i=1;i<n-1;++i) for (let j=1;j<n-1;++j) {
    const w=entry(k,i,j);
    if (w===0n) continue;
    const a=3*grid[i]+(grid[i]<0?-2:2), b=a+3;
    const c=3*grid[j]+(grid[j]<0?-2:2), d=c+3;
    const area=18-corner2(a,b,c,d,3*(n-k))-corner2(-b,-a,-d,-c,3*(n-k))
      -corner2(a,b,-d,-c,3*k)-corner2(-b,-a,c,d,3*k);
    assert(Number.isInteger(area) && area>=0 && area<=18,"clipped pair area");
    total+=BigInt((n-k)*area)*w;
  }
  return piSquared(total*unit,18n*N*N*fieldScale,true);
}
const metricCeil=1341640787n, metricDen=10n**9n;
assert(5n*metricCeil**2n>=9n*metricDen**2n,"3/sqrt(5) upper bound");
const outer=outerFlux()+piSquared(2n*metricCeil,metricDen*N,true);

// Integer vertices of a piecewise-linear loop uniformly close to a latitude.
// Values are in bins translated by n/2, times T. Evenness and antipodality are exact.
const T=100000, q=4, steps=n*q;
assert(T%q===0,"triangular loop grid");
function latitude(width) {
  if (width===0) return Array.from({length:steps+1},(_,m)=>(steps-m)*(T/q));
  const R=cosPi(width,n), sample=new Array(steps+1);
  for (let m=0;m<=steps/2;++m) {
    const cs=cosPi(m,steps), prods=[R[0]*cs[0],R[1]*cs[0],R[0]*cs[1],R[1]*cs[1]];
    const targetLo=-prods.reduce((a,b)=>a>b?a:b), targetHi=-prods.reduce((a,b)=>a<b?a:b);
    const proposed=n/2+n*Math.asin(Math.cos(Math.PI*width/n)*Math.cos(Math.PI*m/steps))/Math.PI;
    const v=Math.round(T*proposed);
    assert(cosPi(v-2,n*T)[0]*S>=targetHi && cosPi(v+2,n*T)[1]*S<=targetLo,"latitude enclosure");
    sample[m]=v;
    sample[steps-m]=n*T-v;
  }
  assert(sample[steps/2]===n*T/2,"zero of the profile");
  for (let m=0;m<steps;++m) {
    const dx=sample[m]-sample[m+1];
    assert(dx>=0 && dx*q<=T,"monotonicity and angular Lipschitz constant");
  }
  return sample;
}

// Split the segment at crossings of the x and y bin walls. Exact integer
// fractions give the trapezoidal integral of the y-primitive in each cell.
function walls(stops,start,change) {
  if (!change) return;
  const end=start+change, low=Math.min(start,end), high=Math.max(start,end);
  for (let wall=(Math.floor(low/T)+1)*T;wall<high;wall+=T)
    stops.push([Math.abs(wall-start),Math.abs(change)]);
}
function branchIntegral(rows,x,y,dx,dy,sign) {
  if (!dx) return 0n;
  const stops=[[0,1],[1,1]];
  walls(stops,x,dx);
  walls(stops,y,dy);
  stops.sort(([a,b],[c,d])=>a*d-c*b);
  let total=0n;
  for (let i=1;i<stops.length;++i) {
    const [p,r]=stops[i-1], [v,s]=stops[i];
    const dt=BigInt(v*r-p*s);
    if (dt===0n) continue;
    const twiceDen=2n*BigInt(r*s), sumT=BigInt(p*s+v*r);
    const cell=(a,da)=>Math.min(n-1,Number((BigInt(a)*twiceDen+BigInt(da)*sumT)/(twiceDen*BigInt(T))));
    const a=cell(x,dx), b=cell(y,dy), row=rows[a], w=row[b+1]-row[b];
    const avg=BigInt(T)*row[b]*twiceDen+(BigInt(y-b*T)*twiceDen+BigInt(dy)*sumT)*w;
    const num=BigInt(sign*dx)*dt*avg*unit*digits;
    const den=BigInt(r*s)*twiceDen*BigInt(T)**2n*fieldScale;
    total+=floorDiv(num,den);
  }
  return total;
}
const widths=[0,6,10,12], samples=widths.map(latitude), totals=widths.map(()=>0n);
function sample(v,m) {
  const i=Math.abs(m)%(2*steps);
  return v[i<=steps?i:2*steps-i];
}
for (let k=1;k<n;++k) {
  const rows=Array.from({length:n},(_,a)=>{
    const row=[0n];
    for (let b=0;b<n;++b) row.push(row[b]+entry(k,a,b));
    return row;
  });
  for (const [j,loop] of samples.entries()) {
    let total=0n;
    for (let m=0;m<steps;++m) {
      const x=loop[m+1], dx=loop[m]-x;
      for (const sign of [1,-1]) {
        const i=m-sign*k*q, y=sample(loop,i+1);
        total+=branchIntegral(rows,x,y,dx,sample(loop,i)-y,sign);
      }
    }
    totals[j]+=BigInt(n-k)*total;
  }
}
// Boundary at latitude zero is polygonal already. Its action has an independent exact formula.
const baseLo=piSquared(BASE_NUM,BASE_DEN,false), baseHi=piSquared(BASE_NUM,BASE_DEN,true);
const boundaryLo=piSquared(totals[0],digits*N*N,false);
assert(boundaryLo<=baseHi && baseHi-boundaryLo<10000n,"boundary polygon vs exact old action");
const results=[];
for (let j=1;j<widths.length;++j) {
  const width=widths[j], t=BigInt(width), Q=BigInt(q);
  const polyLo=piSquared(totals[j],digits*N*N,false);
  // Error at a scalar point is at most cot(t*h)*(h/q)^2/8 + 2h/T.
  // The normalized flux of the homotopy is at most 4*pi times that error.
  const error=piSquared(1n,2n*t*N*Q*Q,true)+piSquared(8n,N*BigInt(T),true);
  const capLo=polyLo-error, sinLo=cosPi(n/2-width,n)[0];
  const capArea=ceilDiv(2n*piHi*(S-sinLo)*digits,piUnit*S);
  const slack=capArea-capLo;
  if (width===6) assert(baseHi+slack<615n*digits/100n,"deep-only ceiling");
  if (width===10) assert(outer+slack<=6148325785606n,"ten-bin ceiling");
  if (width===12) assert(615n*digits/100n-outer-slack>=8986291617n,"required twelve-bin gain");
  results.push({depth_in_bins:width,round_action_lower:format(capLo),round_slack_upper:format(slack),
    deep_only_ceiling:format(baseHi+slack),joint_ceiling:format(outer+slack)});
}
const deltaLo=615n*digits/100n-baseHi, deltaHi=615n*digits/100n-baseLo;
const quarterTurn=[2n,3n,6n].map(m=>{
  const a=(3n*m-4n)**2n, b=9n*m*m;
  const lo=floorDiv(deltaLo*a,b), hi=ceilDiv(deltaHi*a,b);
  assert(m===2n ? hi<8986291617n : lo>8986291617n,"quarter-turn middle gain");
  return {width_in_bins:Number(m),response:[format(lo),format(hi)]};
});
console.log(JSON.stringify({outer_ceiling:format(outer),subintervals_per_half_circle:steps,
  boundary_check_gap_in_trillionths:String(baseHi-boundaryLo),bands:results,quarter_turn:quarterTurn},null,2));
