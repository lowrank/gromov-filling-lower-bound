"use strict";

// Bound how much a comass-one correction can gain on two explicit hemisphere regions.
const path = require("node:path");
const {assert,piInterval} = require("./issue163_fourier_caps.cjs");
const {cosPi,S} = require("./issue163_hemisphere_cap.cjs");
const {loadCorner,HERM_DEN,BASE_NUM,BASE_DEN} = require("./issue163_midpoint.cjs");
const n = 112, gaps = 2*n, parts = 256;
const bins = gaps*1e8, T = BigInt(bins), tolerance = 6;
const floor = (x,y) => x/y - (x%y < 0n ? 1n : 0n);
const ceil = (x,y) => -floor(-x,y);
const min = (x,y) => x < y ? x : y;
const max = (x,y) => x > y ? x : y;
const fraction = (x,y) => [floor(S*x,y),ceil(S*x,y)];
const add = (a,b) => [a[0]+b[0],a[1]+b[1]];
const sub = (a,b) => [a[0]-b[1],a[1]-b[0]];
function mul(a,b) {
  const p = [a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]];
  return [floor(p.reduce(min),S),ceil(p.reduce(max),S)];
}
const one = [S,S], scaled = (a,x) => [a[0]*BigInt(x),a[1]*BigInt(x)];
const rawPi = piInterval(), pi = [floor(rawPi[0],10n**16n),ceil(rawPi[1],10n**16n)];
const pi2 = mul(pi,pi);

function halfArc(ball) {
  if (ball) return {lo:1,hi:1,den:2};
  // The endpoints and the two centers make two equilateral spherical triangles.
  const c = cosPi(1,n), den = 1e11;
  const proposal = Math.acos(Math.cos(Math.PI/n)/(1+Math.cos(Math.PI/n)))/Math.PI;
  const lo = Math.floor(den*proposal)-1, hi = Math.ceil(den*proposal)+1;
  const ratio = [floor(S*c[0],S+c[0]),ceil(S*c[1],S+c[1])];
  assert(cosPi(lo,den)[0] >= ratio[1] && cosPi(hi,den)[1] <= ratio[0], "spherical triangle angle");
  return {lo,hi,den};
}

function regionBudget(ball, w, cap) {
  const rDen = ball ? 2*n : n;
  const c = cosPi(1,rDen), s = cosPi(rDen/2-1,rDen);
  const arc = halfArc(ball);
  const angle = mul(pi,[fraction(BigInt(arc.lo),BigInt(arc.den))[0],
                        fraction(BigInt(arc.hi),BigInt(arc.den))[1]]);
  const trueArea = ball ? mul(pi,sub(one,c)) : sub(pi,mul(add(one,scaled(c,2)),angle));
  const length = mul(angle,s);
  const anchor = Array.from({length:n},(_,i) => {
    const delta = 2*i + (ball ? 1 : 0);
    return {a:mul(c,cosPi(delta,2*n)), b:mul(s,cosPi(Math.abs(n-delta),2*n))};
  });
  const edges = [];
  for (let i = 0; i < n; ++i) for (let j = i+1; j < n; ++j)
    if (w[i][j] !== 0n) edges.push([i,j,w[i][j]]);
  let previous = Array(n).fill(-T/BigInt(gaps)), chordSum = 0n;
  for (let k = 1; k <= parts; ++k) {
    const ct = [cosPi(k*arc.hi,parts*arc.den)[0],cosPi(k*arc.lo,parts*arc.den)[1]];
    const next = anchor.map(({a,b},i) => {
      const dot = sub(a,mul(b,ct));
      const middle = Number(dot[0]+dot[1])/(2*Number(S));
      const q = Math.round(bins*Math.acos(Math.max(-1,Math.min(1,middle)))/Math.PI);
      const lo = Math.max(0,q-tolerance), hi = Math.min(bins,q+tolerance);
      assert((lo === 0 || cosPi(lo,bins)[0] >= dot[1]) &&
             (hi === bins || cosPi(hi,bins)[1] <= dot[0]), "spherical distance enclosure");
      return BigInt((2*i+1)*(bins/gaps)-q);
    });
    for (const [i,j,b] of edges)
      chordSum += b*(previous[i]*next[j]-previous[j]*next[i]);
    previous = next;
  }
  // Two reflected oriented arcs contribute the negative of this entire sum.
  const polygon = mul(pi2,fraction(-2n*chordSum*10n**12n,HERM_DEN*T*T*cap));
  const radius = mul(pi,fraction(1n,BigInt(gaps))), eps = mul(pi,fraction(BigInt(tolerance),T));
  const chordError = mul(mul(length,length),fraction(1n,BigInt(parts)));
  const roundError = scaled(mul(eps,add(scaled(radius,2),eps)),2*parts);
  const error = add(chordError,roundError)[1];
  const flux = [polygon[0]-error,polygon[1]+error];
  const base = mul(pi2,fraction(BASE_NUM,BASE_DEN));
  const budget = add(base,scaled(sub(trueArea,flux),gaps));
  return {parts_per_half_arc:parts, ceiling_interval_1e9:
    [floor(budget[0]*10n**9n,S).toString(),ceil(budget[1]*10n**9n,S).toString()]};
}

const {w,cap} = loadCorner(process.argv[2] || path.join(__dirname,"issue163_inputs"));
const balls = regionBudget(true,w,cap), lenses = regionBudget(false,w,cap);
assert(BigInt(balls.ceiling_interval_1e9[1]) < 6150000000n, "midpoint ball ceiling");
assert(BigInt(lenses.ceiling_interval_1e9[0]) > 6150000000n, "hemisphere lens budget");
console.log(JSON.stringify({intrinsic_midpoint_balls:balls, adjacent_anchor_lenses:lenses},null,2));
