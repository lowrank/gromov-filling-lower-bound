"use strict";

const path = require("node:path");
const {assert, piInterval} = require("./issue163_fourier_caps.cjs");
const {checkGram, cholesky} = require("./issue163_reweighted_field.cjs");
const {HERM_DEN: H, loadProfile, pinned} = require("./issue163_midpoint.cjs");
const shapes = require("./issue163_slice_diagonals.json");
const original = require("./issue163_planar_witness.json");
const tents = JSON.parse(pinned(__dirname, "issue163_midpoint_witness.json",
  "6b2ff56ac80847de59d0d1a0f4b54a68a4adc6e84ec8659b33ec66c7615f0596"));
const dir = process.argv[2] || path.join(__dirname, "issue163_inputs");
const n = 112, markers = Object.keys(shapes.shapes).map(Number).sort((a,b)=>a-b);
const sum = xs=>xs.reduce((a,b)=>a+b,0n);
const phases = original.neighbor_planar_vectors.map(row=>row.map(BigInt));
const phaseDen = BigInt(original.phase_denominator);
assert(markers[0]===0 && markers[1]===1 && markers.at(-1)===55, "diagonal interpolation endpoints");
for (const row of [...Object.values(shapes.shapes),shapes.right_child]) {
  assert(row.length===n && row.every(x=>Number.isSafeInteger(x) && x>0), "positive diagonal proposal");
  assert(Math.abs(row.reduce((a,b)=>a+b)-shapes.scale)<=n, "normalized shape");
}
assert(phases.length===n && phases.every(([x,y])=>x*x+y*y<=phaseDen**2n), "planar unit disks");
function det(a,b) {return a[0]*b[1]-a[1]*b[0];}
function action(w,z) {
  let q=0n;
  for (let i=0;i<n;++i) for (let j=i+1;j<n;++j) q+=2n*w[i][j]*det(z[i],z[j]);
  return q;
}
function wedge(w,i,j,value) {w[i][j]+=value; w[j][i]-=value;}
function localTerms(w) {
  for (const [j,c] of [[2,17n],[110,-17n],[4,2n],[108,-2n]]) {
    const v=c*(H/2000n);
    wedge(w,0,j,v);
    wedge(w,110-j,110,v);
  }
}
// Reflection about the anchor at -h fixes label 111 and negates the others.
function reflectCheck(w,reflected) {
  const index=j=>j===111?111:110-j;
  const sign=j=>j===111?1n:-1n;
  for (let i=0;i<n;++i) for (let j=i+1;j<n;++j)
    assert(reflected[i][j]===-sign(i)*sign(j)*w[index(i)][index(j)], "reflected prefix matrix");
}
function addChild(w,right) {
  const t=tents.bisection, half=t.parent_half, den=BigInt(tents.denominator);
  const parent=half.concat(half.slice().reverse());
  assert(H%(2n*den)===0n, "corner coefficient units");
  for (let j=0;j<n;++j) {
    wedge(w,0,j,BigInt(parent[j])*(H/(2n*den)));
    wedge(w,right?111:0,j,BigInt(t.child[j])*(right?-1n:1n)*(H/(2n*den)));
  }
}
// Only the relative diagonal shape is interpolated. Its final trace is rounded down.
function diagonal(k,budget) {
  let shape;
  if (k==="right") shape=shapes.right_child.map(BigInt);
  else {
    const r=markers.find(m=>m>=k), l=r===k?k:markers[markers.indexOf(r)-1];
    shape=shapes.shapes[l].map((v,j)=>l===r?BigInt(v):
      BigInt(r-k)*BigInt(v)+BigInt(k-l)*BigInt(shapes.shapes[r][j]));
  }
  const total=sum(shape);
  return shape.map(v=>budget*v/total);
}
function certify(w,k,budget) {
  const d=diagonal(k,budget), edge=w.flat();
  assert(sum(d)<=budget && d.every(v=>v>0n), "trace budget");
  // Floating point proposes a factor of a shifted matrix. The Gram residual,
  // the strict trace target and every matrix coefficient are tested by integers.
  const xy=cholesky(d.map(Number),edge.map(Number),n,1e-9,Number(H));
  assert(xy && checkGram(d,edge,n,xy,H), "integer Gram residual for cell "+k);
}
const rawValueDen=H*phaseDen**2n, single=phases.slice();
single[83]=single[7];
let oldFloor, onePairFloor, correctedFloor;
for (let k=0;k<=55;++k) {
  const bins=Array.from({length:n},(_,i)=>111-i-Number(i<k));
  const {w}=loadProfile(dir,bins);
  const mirrorBins=Array.from({length:n},(_,i)=>111-i-Number(i<111-k));
  const mirror=loadProfile(dir,mirrorBins).w;
  if (k===0) {
    reflectCheck(w,mirror);
    const right=w.map(row=>row.slice());
    addChild(right,true);
    localTerms(right);
    certify(right,"right",H*9909n/10000n);
    addChild(w,false);
  }
  if (k===28) {
    const oldScaled=action(w,phases)*10n**9n, singleScaled=action(w,single)*10n**9n;
    oldFloor=oldScaled/rawValueDen;
    onePairFloor=singleScaled/rawValueDen;
    assert(oldScaled>999701031n*rawValueDen && singleScaled>994961123n*rawValueDen &&
      det(phases[0],single[83])===det(phases[0],single[7]),
      "unchanged single-pair test");
  }
  localTerms(w);
  if (k>0) {
    localTerms(mirror);
    reflectCheck(w,mirror);
  }
  certify(w,k,k===28 ? H*98936n/100000n : H*9909n/10000n);
  if (k===28) correctedFloor=action(w,phases)*10n**9n/rawValueDen;
}
// Unit directions obtained by normalizing the three recorded rational vectors.
function unitDetBound(j,num,den,lower) {
  const a=phases[0], b=phases[j], w=det(a,b);
  const lhs=(den*w)**2n, rhs=num**2n*sum(a.map(x=>x*x))*sum(b.map(x=>x*x));
  assert(w>0n && (lower ? lhs>rhs : lhs<rhs), "normalized transverse component "+j);
}
unitDetBound(7,16n,100n,false);
unitDetBound(83,999n,1000n,true);
// At each large L the same scalar cell can carry one active central anchor.
const L=1000000, e=Array.from({length:n},(_,i)=>2*i-55);
e[0]=-3*L/5; e[110]=61*L/100; e[111]=62*L/100;
const P=e.map((v,i)=>L*(55-i)+v), signed=P.concat(P.map(v=>-v));
const active=signed.map((v,i)=>({i,r:56*L-v})).filter(({r})=>L/2<r && r<3*L/2);
assert(signed.every((v,i)=>Math.abs(v-signed[(i+1)%signed.length])<L), "angular Lipschitz bounds");
assert(P.every((v,i)=>Math.floor(v/L+56)===111-i-Number(i<28)) &&
  signed.filter(v=>v>55*L).length===1, "same free cell");
assert(active.length===1 && active[0].i===223 && P[55]===55, "central anchor and linear sign");
const contrast=17*(e[1]-e[109])+2*(e[3]-e[107]);
assert(contrast===-4088 && 2*55*38+2*Math.abs(contrast)===12356, "raw error at most 12.356/L");
const [lo,hi]=piInterval(), unit=10n**48n;
const actionNum=737877064811692678202731938521n, actionDen=1194666547200000000000000000000n;
const thresholdNum=actionNum*9999999n*100n, thresholdDen=actionDen*10000000n*615n;
assert(9909n*thresholdDen*unit**2n<10000n*thresholdNum*lo**2n &&
  994961123n*thresholdDen*unit**2n>10n**9n*thresholdNum*hi**2n, "target lies between the local tests");
assert(actionNum*hi**2n*9999999n*10n**15n <
  6097712n*unit**2n*actionDen*10000000n*999701031n, "ceiling on uniform rescaling");
const decimal=10n**12n, target=615n*decimal/100n;
const bFloor=actionNum*lo**2n*decimal/(actionDen*unit**2n);
const cNum=2213639035555078034608195815563n, cDen=3583999641600000000000000000000n;
const ceil=(a,b)=>(a+b-1n)/b;
for (const [t,area,frac,q] of [[5,310111,4199,564386],[10,612127,9153,411075],
    [22,1303938,20502,285087],[40,2254225,36091,217790]].map(row=>row.map(BigInt))) {
  const h=2n*lo*t*decimal/(100n*unit)-ceil(t*t*cDen*decimal,10000n*cNum);
  assert(10n**6n*h>area*decimal && (bFloor+h-target)*10n**5n>frac*bFloor, "collar area and trace");
  const y=target-bFloor;
  assert(0n<y && y<h && q*q*h*h>10n**12n*(2n*h*y-y*y), "necessary collar RMS");
  if (t===22n) {
    const root=953939202n, scale=10n**9n;
    assert(100n*root*root>91n*scale*scale &&
      (bFloor*scale+h*(scale-root))*10n**6n>6155949n*decimal*scale, "width 0.22 implication");
  }
}
assert(5n*lo**2n*10n**6n>425413n*116n*unit**2n, "compensating area");
console.log(JSON.stringify({verified_matrices:57,diagonal_shapes:markers.length+1,uniform_local_budget:"0.9909",
  cell_28_budget:"0.98936",original_floor_1e9:String(oldFloor),one_pair_floor_1e9:String(onePairFloor),
  corrected_witness_floor_1e9:String(correctedFloor),central_anchor_error:"12.356/L"}));
