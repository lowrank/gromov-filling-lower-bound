"use strict";

const path = require("node:path");
const {assert, piInterval} = require("./issue163_fourier_caps.cjs");
const {cholesky, checkGram} = require("./issue163_reweighted_field.cjs");
const {loadCorner, loadProfile, pinned, HERM_DEN: H, BASE_NUM, BASE_DEN} = require("./issue163_midpoint.cjs");
const diagonals = require("./issue163_anchor_diagonals.json");
const gap = JSON.parse(pinned(__dirname, "issue163_midpoint_witness.json",
  "6b2ff56ac80847de59d0d1a0f4b54a68a4adc6e84ec8659b33ec66c7615f0596"));

const n=112, input=process.argv[2] || path.join(__dirname,"issue163_inputs");
const capNum=9999999n, capDen=10000000n, micro=1000000n;
const oldNum=1933n, oldDen=2500n;
const half=[6500,-2040,-800,-200,0,0,0,-900,...Array(12).fill(-60),...Array(35).fill(-4)];
const c=[...half,0,...half.slice().reverse()].map(BigInt);
const sum=row=>row.reduce((a,b)=>a+b,0n);
assert(c.length===n-1 && sum(c)===3400n, "signed coefficients of the one-anchor primitive");

function wedge(w,i,j,x) {w[i][j]+=x; w[j][i]-=x;}
function addAnchors(w,two) {
  for (let i=0;i<n-1;++i) {
    const v=c[i]*(H/(2n*micro));
    wedge(w,i,n-1,v);
    if (two) wedge(w,0,i+1,v);
  }
}
const scale=1000000000n;
assert(H%scale===0n && H%(2n*micro)===0n, "diagonal and anchor units");
let tested=0, worst=0n;
const traces=[];
function check(w) {
  const raw=diagonals[tested++];
  assert(Array.isArray(raw) && raw.length===n && raw.every(x=>Number.isSafeInteger(x) && x>0),
    "positive diagonal entries");
  const trace=sum(raw.map(BigInt));
  traces.push(trace);
  assert(trace*capDen<=scale*capNum,"trace "+tested);
  if (trace>worst) worst=trace;
  const d=raw.map(v=>BigInt(v)*(H/scale)), edge=w.flat();
  const xy=cholesky(d.map(Number),edge.map(Number),n,1e-9,Number(H));
  assert(xy && checkGram(d,edge,n,xy,H), "integer Gram residual "+tested);
}
const {w:corner}=loadCorner(input);
const halfParent=gap.bisection.parent_half;
const parent=halfParent.concat(halfParent.slice().reverse()).map(BigInt);
const child=gap.bisection.child.map(BigInt), gapDen=BigInt(gap.denominator);
assert(parent.length===n && child.length===n && H%(2n*oldDen*gapDen)===0n,"old gap units");
const gapUnit=oldNum*(H/(2n*oldDen*gapDen));
for (const chamber of ["parent","left","right"]) {
  const w=corner.map(row=>row.slice());
  for (let j=0;j<n;++j) {
    wedge(w,0,j,gapUnit*parent[j]);
    if (chamber==="left") wedge(w,0,j,gapUnit*child[j]);
    if (chamber==="right") wedge(w,n-1,j,-gapUnit*child[j]);
  }
  addAnchors(w,true);
  check(w);
}
const prefix=k=>Array.from({length:n},(_,j)=>n-1-j-Number(j<k));
for (let k=1;k<=55;++k) {
  const {w}=loadProfile(input,prefix(k));
  const {w:other}=loadProfile(input,prefix(n-1-k));
  addAnchors(w,false);
  addAnchors(other,false);
  const idx=i=>i===n-1?n-1:n-2-i;
  for (let i=0;i<n;++i) for (let j=i+1;j<n;++j) {
    const sign=j===n-1?1n:-1n;
    assert(other[i][j]===sign*w[idx(i)][idx(j)], "reflection about the active anchor");
  }
  check(w);
}
assert(tested===58 && diagonals.length===tested,"chamber count");

// 224 gap and anchor tents. Integrate their known triangular boundary traces.
const N=BigInt(n);
const gainNum=oldNum*(2n*sum(parent)+sum(child))*micro+
  8n*gapDen*oldDen*sum(c);
const gainDen=4n*N*gapDen*oldDen*micro;
let num=BASE_NUM*gainDen*capNum + gainNum*capDen*BASE_DEN;
let den=BASE_DEN*gainDen*capNum;
function gcd(a,b) {while(b) [a,b]=[b,a%b]; return a;}
const g=gcd(num,den); num/=g; den/=g;
const [lo,hi]=piInterval(), places=10n**18n, piUnits=10n**96n;
const floor=num*lo**2n*places/(den*piUnits);
assert(floor===num*hi**2n*places/(den*piUnits) && floor>6096200000000000000n, "directed area floor");
// The three double-anchor chambers carry fixed fractions of a projected triangle.
const rawCap=scale*capNum/capDen;
assert(rawCap*capDen===scale*capNum,"raw trace units");
const [parentLoss,leftLoss,rightLoss]=traces.slice(0,3).map(t=>rawCap-t);
const minimumLoss=rawCap-worst;
const qDen=12n*N*num, qNum=18n*N*num-7n*den;
assert(100n*qNum>149n*qDen && minimumLoss>0n, "mean area covered by a rotated grid");
const reserveNum=((2n*parentLoss+leftLoss+rightLoss)*qDen+
  4n*minimumLoss*(qNum-qDen))*capDen;
const reserveDen=4n*qDen*scale*N*capNum;
let occupationNum=num*reserveDen+den*reserveNum, occupationDen=den*reserveDen;
const divisor=gcd(occupationNum,occupationDen);
occupationNum/=divisor;
occupationDen/=divisor;
const finalFloor=occupationNum*lo**2n*places/(occupationDen*piUnits);
assert(finalFloor===occupationNum*hi**2n*places/(occupationDen*piUnits) &&
  finalFloor===6096292737690900167n,"area floor after grid rotation");
const lowerDecimal=v=>(v/places)+"."+(v%places).toString().padStart(18,"0");
console.log(JSON.stringify({chambers:tested,maximum_trace_in_billionths:String(worst),
  sum_microcoefficients:String(sum(c)),pi_squared_factor:num+"/"+den,
  area_floor:lowerDecimal(floor),
  double_anchor_raw_reserves_in_billionths:[parentLoss,leftLoss,rightLoss].map(String),
  occupation_pi_squared_factor:occupationNum+"/"+occupationDen,
  occupation_area_floor:lowerDecimal(finalFloor)},null,2));
