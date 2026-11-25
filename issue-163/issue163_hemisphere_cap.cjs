"use strict";

const { parentField, U } = require("./issue163_signed_endpoint_ceiling.cjs");
const { piInterval, assert } = require("./issue163_fourier_caps.cjs");
const n = 112, parts = n*1024;
const T = 1000000000, grid = BigInt(T), W = 10n**9n;
const S = 10n**32n, pi = piInterval(), digits = 10n**12n;
const ceil = (a,b) => a/b + (a%b > 0n ? 1n : 0n);
const min = (a,b) => a < b ? a : b;
const max = (a,b) => a > b ? a : b;

function cosPi(num,den) {
  // Return directed enclosures in units of 1/S. All callers use [0,pi].
  assert(Number.isSafeInteger(num) && Number.isSafeInteger(den) && num >= 0 && num <= den, "cosine angle");
  if (2*num > den) {
    const [lo,hi] = cosPi(den-num,den);
    return [-hi,-lo];
  }
  const d = BigInt(den)*10n**16n, j = BigInt(num);
  const x0 = pi[0]*j/d, x1 = ceil(pi[1]*j,d);
  let a = S, b = S, lo = S, hi = S;
  for (let k = 1; k <= 23; k++) {
    const divisor = S*S*BigInt(2*k-1)*BigInt(2*k);
    a = a*x0*x0/divisor;
    b = ceil(b*x1*x1,divisor);
    if (k%2) { lo -= b; hi -= a; }
    else { lo += a; hi += b; }
  }
  return [lo,hi+ceil(b*x1*x1,S*S*47n*48n)];
}

function enclosedBoundary(width) {
  const r = cosPi(width,2*n), low = [], high = [];
  const proposalR = Math.cos(width*Math.PI/(2*n));
  for (let i = 0; i <= parts; i++) {
    const ct = cosPi(i,parts);
    const products = [r[0]*ct[0],r[0]*ct[1],r[1]*ct[0],r[1]*ct[1]];
    const targetLo = -products.reduce(max), targetHi = -products.reduce(min);
    // x = n/2 + (n/pi) asin(r cos theta). The proposal is accepted only
    // after checking cos(pi*x/n) = -r cos(theta) on both sides.
    const x = n/2+n*Math.asin(proposalR*Math.cos(Math.PI*i/parts))/Math.PI;
    const a = Math.floor(T*x)-1, b = Math.ceil(T*x)+1;
    assert(cosPi(a,n*T)[0]*S >= targetHi && cosPi(b,n*T)[1]*S <= targetLo, "inverse cosine enclosure");
    low.push(a); high.push(b);
  }
  function reflect(i) {
    const j = Math.abs(i)%(2*parts);
    return j > parts ? 2*parts-j : j;
  }
  return {low:i => low[reflect(i)], high:i => high[reflect(i)]};
}

function signedRows(k,parent) {
  const positive = [], negative = [];
  for (let a = 0; a < n; a++) {
    const pos = [0n], neg = [0n];
    for (let b = 0; b < n; b++) {
      const valid = Math.abs(a-b) <= k && Math.abs(a+b-n+1) <= n-k;
      const w = valid ? ceil(2n*W*parent(2*k,2*a,2*b),U) : 0n;
      pos.push(pos[b]+max(0n,w));
      neg.push(neg[b]+min(0n,w));
    }
    positive.push(pos); negative.push(neg);
  }
  return {positive,negative};
}

function yPrimitive(prefix,y) {
  const j = Math.min(n-1,Math.floor(y/T));
  return grid*prefix[j]+BigInt(y-j*T)*(prefix[j+1]-prefix[j]);
}

function rectangle(rows,x0,x1,y0,y1) {
  if (x1 <= x0 || y1 <= y0) return 0n;
  let total = 0n;
  for (let a = Math.floor(x0/T); a*T < x1; a++) {
    const width = Math.min(x1,(a+1)*T)-Math.max(x0,a*T);
    total += BigInt(width)*(yPrimitive(rows[a],y1)-yPrimitive(rows[a],y0));
  }
  return total;
}

function capIntegral(parent,width) {
  const {low,high} = enclosedBoundary(width);
  let area = 0n;
  for (let k = 1; k < n; k++) {
    const {positive,negative} = signedRows(k,parent), shift = k*(parts/n);
    let integral = 0n;
    for (let i = 0; i < parts; i++) {
      const a = i+shift, b = i-shift;
      integral += rectangle(positive,low(i+1),high(i),
        Math.min(low(a),low(a+1)),Math.max(high(b),high(b+1)));
      integral += rectangle(negative,high(i+1),low(i),
        Math.max(high(a),high(a+1)),Math.min(low(b),low(b+1)));
    }
    area += BigInt(n-k)*integral;
  }
  assert(area > 0n, "positive cap action");
  return ceil(digits*area*pi[1]**2n,BigInt(n)**2n*grid**2n*W*10n**96n);
}

function verifyScaleAtPole(parent) {
  // Limit along longitude pi/448 into the two central scalar cells.
  const labels = Array.from({length:2*n}, (_,i) => i <= n ? n : n-1);
  const sine = Array.from({length:2*n}, (_,k) => cosPi(Math.abs(n-k),2*n));
  let val = 0n;
  for (let i = 0; i < labels.length; i++) for (let j = i+1; j < labels.length; j++) {
    const w = parent(j-i,labels[i],labels[j]);
    val += w*sine[j-i][w >= 0n ? 0 : 1];
  }
  assert(50019n*val > 50000n*U*S, "hemisphere limit bounds the scale");
}

module.exports = { cosPi, S };

if (require.main === module) {
  const dir = process.argv[2];
  if (!dir) throw Error("Pass the finite certificate directory.");
  const field = parentField(dir);
  verifyScaleAtPole(field);
  const report = {};
  for (const width of [1,2]) {
    const cap = capIntegral(field,width);
    const sinUpper = cosPi(n-width,2*n)[1];
    const belt = ceil(digits*2n*pi[1]*sinUpper,10n**48n*S);
    const correction = 6300000n; // 0.0000063 in the displayed units.
    const frozen = cap+correction+belt;
    const rescaled = ceil(50019n*(cap+correction),50000n)+belt;
    assert(rescaled < (width === 1 ? 6150000000000n : 6170000000000n), "cap ceiling");
    report[448/width] = {angular_subintervals:parts, cap_upper_1e12:String(cap),
      belt_upper_1e12:String(belt), fixed_scale_upper_1e12:String(frozen),
      flexible_scale_upper_1e12:String(rescaled)};
  }
  console.log(JSON.stringify(report,null,2));
}
