"use strict";

// Exact boundary action, loss at each clipped vertex, and a ceiling on every clipping scale.
const path = require("node:path");
const zlib = require("node:zlib");
const {assert, INPUT, npzReader, piInterval} = require("./issue163_fourier_caps.cjs");
const {readCorrection, makeLevel} = require("./issue163_free_field.cjs");
const {loadCorner, pinned, HERM_DEN} = require("./issue163_midpoint.cjs");
const witness = require("./issue163_midpoint_witness.json");
const n = 112, N = BigInt(n), unit = 10n**12n, den = BigInt(witness.denominator);
const q = witness.bisection, dir = process.argv[2] || path.join(__dirname, "issue163_inputs");
const sum = xs => xs.reduce((a,b) => a+b, 0n);
function gcd(a,b) { while (b) [a,b] = [b,a%b]; return a; }
function ceiling(a,b) { assert(a >= 0n && b > 0n, "positive quotient"); return (a+b-1n)/b; }

const {w,cap} = loadCorner(dir);
const endpoint = BigInt(q.parent_half[0]) + BigInt(q.child[n-1]);
const lossNum = 2n*N*unit*(2n*sum(w[0])*den + endpoint*HERM_DEN);
const lossDen = cap*den*HERM_DEN, g = gcd(lossNum,lossDen);
const [piLo,piHi] = piInterval(), piUnits = 10n**48n;
assert(106n*piLo > 333n*piUnits && 113n*piHi < 355n*piUnits, "rational pi bounds");
// The first four positive terms of 2 atanh(1/3) give log(2) > 6931/10000.
const logDen = 3n**7n * 3n * 5n * 7n;
const logNum = 2n*sum([1n,3n,5n,7n].map(k => logDen/(k*3n**k)));
assert(10000n*logNum > 6931n*logDen, "logarithm lower bound");
// [(684 log(2) + 23/16)/(2 pi)] - C > 1/16.
const a = (684n*6931n*16n + 23n*10000n)*113n, b = 16n*10000n*710n;
assert(16n*(a*lossDen-b*lossNum) > b*lossDen, "positive all-genus correction");
assert(2n*lossNum > 151n*lossDen && lossNum < 76n*lossDen, "corner loss");
// pi*C/4-2 > 57+1/4. Use exp(1) > sum_{k=0}^6 1/k! and exp(1/4) > 5/4.
assert(333n*lossNum > 237n*106n*lossDen &&
  15n*1957n**57n > 8n*10n**25n*720n**57n, "small-shift ceiling below 2e-25");

// On one gap only the first and last coordinates can be clipped.
// Reflection deals with the other parent chamber by swapping these two row tests.
const parent = q.parent_half.concat(q.parent_half.slice().reverse()).map(BigInt);
const child = q.child.map(BigInt), e = n-1, matrixUnit = HERM_DEN/den;
assert(HERM_DEN%den === 0n, "corner units");
for (const [row,v] of [[null,null],[0,child],[e,child]]) {
  const y = w.map(r => r.map(x => 2n*x)); // HERM_DEN times the actual skew matrix
  function wedgeAt(i,b,sign) {
    for (let j=0; j<n; ++j) {
      const step = sign*matrixUnit*b[j];
      y[i][j] += step;
      y[j][i] -= step;
    }
  }
  wedgeAt(0,parent,1n);
  if (row !== null) wedgeAt(row,v,row === 0 ? 1n : -1n);
  const edge = y[0][e] > 0n ? y[0][e] : 0n;
  for (const inward of [sum(y[0]),-sum(y[e])])
    assert(8n*unit*(inward-edge) > cap*HERM_DEN, "loss along a two-coordinate ribbon");
}

// The m-th ring disappears between clipping depths mh and (m+1)h.
const archive = name => npzReader(pinned(dir,...INPUT[name]), zlib.inflateRawSync);
const maps = archive("maps"), base = archive("field")("master_numerators");
const correction = readCorrection(path.join(__dirname,"issue163_free_coefficients.json"),base.length);
const grid = Array.from({length:n+1},(_,i) => i-n/2);
const level = makeLevel({n,grid,boxes:[]},maps,base,correction.delta,null);
const reps = maps("reps_112"), counts = maps("objective_num_112"), divisors = maps("objective_den_112");
const positive = Array(n/2).fill(0n), negative = Array(n/2).fill(0n);
for (let j=0; j<level.w.length; ++j) {
  const x = reps[3*j+1], y = reps[3*j+2], ring = Math.min(x,y,n-1-x,n-1-y);
  const twice = 2n*BigInt(counts[j]), d = BigInt(divisors[j]);
  assert(d > 0n && twice%d === 0n, "half-cell area count");
  const mass = (twice/d)*level.w[j]*BigInt(level.scalar[x])*BigInt(level.scalar[y]);
  (mass >= 0n ? positive : negative)[ring] += mass;
}
assert(sum(positive)+sum(negative) === level.action &&
  level.action === 2478905598010270233961179313430560n, "signed ring actions");

const actionDen = N*N*32n*10n**16n*cap;
let maximum = 0n, worstBin;
for (let m=1; m<n/2; ++m) {
  const j = BigInt(m+1), pair = sum(positive.slice(m)) + sum(negative.slice(m+1));
  const pairUpper = ceiling(unit*pair*355n**2n,actionDen*113n**2n);
  // At t = j*pi/n use log(1/t) < 4 and log(1/t) <= 1/t-1.
  const energyUpper = [
    ceiling(unit*44n*355n*j*j,113n*N*N),
    ceiling(unit*(8n*j*113n*N+4n*355n*j*j),113n*N*N),
    ceiling(unit*16n*115n*106n,108n*333n)
  ].reduce((a,b) => a < b ? a : b);
  const upper = pairUpper + energyUpper;
  if (upper > maximum) { maximum = upper; worstBin = m; }
}
assert(maximum < 6086n*unit/1000n, "uniform-splitting ceiling at shifts of at least one bin");
console.log(JSON.stringify({corner_loss: (lossNum/g)+"/"+(lossDen/g),
  epsilon:"2^-684", strict_gain:"2^-1372", clipping_intervals_above_one_bin:n/2-1,
  upper_above_one_bin_in_trillionths:String(maximum), largest_upper_on_interval:[worstBin,worstBin+1]},null,2));
