"use strict";

// This scalar replay uses the twelve positive Hermitian comparisons established
// by issue163_planar_comass.cjs. It requires no new matrix witnesses.
const {assert, piInterval} = require("./issue163_fourier_caps.cjs");
const {pinned} = require("./issue163_midpoint.cjs");
const old = JSON.parse(pinned(__dirname,"issue163_midpoint_witness.json",
  "6b2ff56ac80847de59d0d1a0f4b54a68a4adc6e84ec8659b33ec66c7615f0596"));
const src = JSON.parse(pinned(__dirname,"issue163_planar_witness.json",
  "c68acffd8bc66d90e359550a783cac92c0b31fe7817577a374075167d36350e9"));
const den=10n**14n, unit=10n**12n, cap=999999900000n, t=den/1000n, n=112n;
assert(BigInt(old.denominator)===den && BigInt(src.diagonal_denominator)===den, "diagonal units");
const sum=xs=>xs.reduce((a,b)=>a+b,0n);
const axes=[[1n,0n],[0n,-1n],[-1n,0n],[0n,1n]]; // Re(sigma*q) for q=x+iy
const gains={parent:224200n,left:272380n,right:259360n}; // units of 10^-9

// The rectangle makes the intersection bounded. Check all feasible vertices
// of a*x+b*y <= c. A convex polygon's maximum squared radius occurs at a vertex.
function circleExcluded(lines) {
  let count=0;
  for (let i=0; i<lines.length; ++i) for (let j=0; j<i; ++j) {
    const [a,b,c]=lines[i], [d,e,f]=lines[j];
    let det=a*e-b*d;
    if (!det) continue;
    let x=c*e-b*f, y=a*f-c*d;
    if (det<0n) {det=-det; x=-x; y=-y;}
    if (lines.some(([l,m,r])=>l*x+m*y>r*det)) continue;
    assert(x*x+y*y<det*det,"a feasible phase vertex reaches the unit circle");
    ++count;
  }
  assert(count>=3,"phase polygon vertices");
  return count;
}
function check(name) {
  const orig=old.bisection[name+"_diagonal"].map(BigInt);
  const rows=src.diagonals[name].map(row=>row.map(BigInt));
  const bound=cap*(den/unit)-gains[name]*(den/10n**9n);
  const lines=axes.map(([x,y],i)=>[x*t,y*t,sum(rows[i])-bound]);
  const reserves=[];
  for (const a of [2n,3n]) {
    const b=4n-a;
    let removed=0n;
    for (let i=0; i<Number(n); ++i) {
      const r=rows[2][i], s=rows[3][i], pivot=i===3 || i===110;
      // Four times the variance weight, rounded down in original diagonal units.
      const lower=pivot ? 0n : a*b*(r-s)**2n/(b*r+a*s+4n*orig[i]);
      const effective=a*r+b*s-lower;
      assert(20n*(effective-(pivot ? 4n*t : 0n))>=4n*19n*orig[i],"retained diagonal weight");
      removed+=lower;
    }
    lines.push([-a*t,b*t,a*sum(rows[2])+b*sum(rows[3])-removed-4n*bound]);
    reserves.push(String(removed));
  }
  return {gain_in_1e9:String(gains[name]), removed_in_four_diagonal_units:reserves,
    phase_polygon_vertices:circleExcluded(lines)};
}

const chambers=Object.fromEntries(Object.keys(gains).map(k=>[k,check(k)]));
const Bnum=737877064811692678202731938521n, Bden=1194666547200000000000000000000n;
const gainSum=(2n*gains.parent+gains.left+gains.right)*1000n;
const gainDen=4n*n*cap;
const num=Bnum*gainDen+Bden*gainSum, divisor=Bden*gainDen;
function gcd(a,b) {while(b) [a,b]=[b,a%b];return a;}
const g=gcd(num,divisor), [lo,hi]=piInterval(), piScaleSq=10n**96n, places=10n**18n;
const floor=num*lo*lo*places/(divisor*piScaleSq);
assert(floor===num*hi*hi*places/(divisor*piScaleSq),"decimal floor");
// At A < 123/20 the weighted rms eigenvalue imbalance is below 0.132362.
// If at least a fifth of the trace weight has imbalance >= 0.30, A > 6.15.
const bLoSq=(Bnum*lo*lo*20n)**2n, targetSq=(Bden*piScaleSq*123n)**2n;
assert(10n**12n*bLoSq>(10n**12n-132362n**2n)*targetSq,"rms threshold");
assert(500n*(Bnum*lo*lo*10n**6n)**2n>491n*(Bden*piScaleSq*6151503n)**2n,"one-fifth threshold");
console.log(JSON.stringify({chambers,retained_diagonal_fraction:"19/20",
  exact_pi_squared_factor:(num/g)+"/"+(divisor/g),
  area_floor:(floor/places)+"."+(floor%places).toString().padStart(18,"0")},null,2));
