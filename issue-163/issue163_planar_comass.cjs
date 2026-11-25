"use strict";

const path = require("node:path");
const {assert, piInterval} = require("./issue163_fourier_caps.cjs");
const {loadCorner,loadProfile,positiveDefinite,pinned,HERM_DEN} = require("./issue163_midpoint.cjs");
const tents = JSON.parse(pinned(__dirname,"issue163_midpoint_witness.json",
  "6b2ff56ac80847de59d0d1a0f4b54a68a4adc6e84ec8659b33ec66c7615f0596"));
const record = require("./issue163_planar_witness.json");
const dir = process.argv[2] || path.join(__dirname,"issue163_inputs");
const n = 112, N = BigInt(n), unit = 10n**12n, H = HERM_DEN;
const {w,cap} = loadCorner(dir), den = BigInt(record.diagonal_denominator);
const phaseDen = BigInt(record.phase_denominator);
assert(den === 10n**14n && phaseDen === 10n**8n && H%(10000n*den) === 0n, "integer units");
const sum = xs => xs.reduce((a,b) => a+b,0n);
function integers(xs,k) {
  assert(Array.isArray(xs) && xs.length === k && xs.every(Number.isSafeInteger), "integer array");
  return xs.map(BigInt);
}
const t = tents.bisection, half = integers(t.parent_half,n/2);
const p = half.concat(half.slice().reverse()), u = integers(t.child,n);
const wedgeUnit = H/(2n*BigInt(tents.denominator));
function wedgeAt(matrix,i,vec,sign) {
  for (let j=0; j<n; ++j) {
    const a = sign*wedgeUnit*vec[j];
    matrix[i][j] += a;
    matrix[j][i] -= a;
  }
}
function value(matrix,rows,rank) {
  assert(rows.length === n, "number of vectors");
  const z = rows.map(row => {
    assert(row.length === rank,"complex vector dimension");
    const v = row.map(x => integers(x,2));
    assert(sum(v.map(([a,b]) => a*a+b*b)) <= phaseDen**2n,"row squared norm");
    return v;
  });
  let num = 0n;
  for (let i=0; i<n; ++i) for (let j=i+1; j<n; ++j) {
    let det = 0n;
    for (let k=0; k<rank; ++k) det += z[i][k][0]*z[j][k][1]-z[i][k][1]*z[j][k][0];
    num += 2n*matrix[i][j]*det;
  }
  return num;
}
const valueDen = H*phaseDen**2n;
const dirs = [[3n,4n],[-4n,3n],[-3n,-4n],[4n,-3n]];
const capInt = cap*(den/unit), gainInt = den/5000n;
const chamberGains = {parent:216362770n, left:264087651n, right:249909075n}; // units of 10^-12
const corner = w.map(r => r.slice());
wedgeAt(corner,0,p,1n);
const relaxed = value(corner,record.parent_relaxed_vectors,3);
assert(10n**9n*relaxed >= 999999812n*valueDen,"relaxed parent value");

const results = {};
for (const [name,index,sign] of [["parent",null,0n],["left",0,1n],["right",n-1,-1n]]) {
  const matrix = corner.map(r => r.slice());
  if (index !== null) wedgeAt(matrix,index,u,sign);
  assert(BigInt(tents.denominator) === den, "common diagonal denominator");
  const original = integers(t[name+"_diagonal"],n);
  const traces = dirs.map(([a,b],k) => {
    const diag = integers(record.diagonals[name][k],n);
    // Reserve the phase error t(1-|z_3 z_110|) as well as 95% of the old weights.
    for (let j=0; j<n; ++j) {
      const phaseCost = (j === 3 || j === 110) ? den/1000n : 0n;
      assert(20n*(diag[j]-phaseCost) >= 19n*original[j], "diagonal deficit reserve");
    }
    const re = diag.map((x,i) => [...Array(i).fill(0n),x*(H/den)]);
    const im = matrix.map((r,i) => r.slice(0,i+1));
    // The off-diagonal penalty is -theta/(2*1000) in the upper triangle.
    re[110][3] -= a*(H/10000n);
    im[110][3] += b*(H/10000n);
    positiveDefinite(re,im);
    return sum(diag);
  });
  function rectangle(gain) {
    const upper = traces.map(tr => 1000n*(tr-capInt+gain));
    const x = upper[0]>upper[2] ? upper[0] : upper[2];
    const y = upper[1]>upper[3] ? upper[1] : upper[3];
    assert(x >= 0n && y >= 0n && x*x+y*y < den*den, "phase rectangle reaches the unit circle");
    return {real_radius_in_1e14:String(x), imaginary_radius_in_1e14:String(y)};
  }
  results[name] = {...rectangle(gainInt), weighted_gain_in_1e12:String(chamberGains[name]),
    weighted_rectangle:rectangle(chamberGains[name]*(den/unit))};
}

// A strict feasible profile outside all tents. Its entries are expressed in h/2000.
const profile = Array.from({length:n},(_,i) => 2000*(55-i)+2*i-55);
const bins = profile.map(x => Math.floor(x/2000+56));
assert(profile.every((x,i) => Math.abs(x-(i+1<n ? profile[i+1] : -profile[0])) < 2000)
  && profile.filter(x => Math.abs(x) > 55*2000).length === 1 &&
  bins.every((x,i) => x === n-1-i-(i<28 ? 1 : 0)), "strict neighbor cell");
const neighbor = loadProfile(dir,bins);
const planar = value(neighbor.w,record.neighbor_planar_vectors.map(z => [z]),1);
assert(10n**9n*planar >= 999701031n*valueDen, "planar value outside the corner");
// Certify the same directions at unit length by comparing them to Lz, L = 1+4e-8.
const scaleNum = phaseDen+4n;
const directions = record.neighbor_planar_vectors.map(row => {
  const [x,y] = integers(row,2), norm = x*x+y*y;
  assert((phaseDen-1n)**2n*phaseDen**2n <= scaleNum**2n*norm &&
    scaleNum**2n*norm <= (phaseDen+1n)**2n*phaseDen**2n, "unit phase enclosure");
  return [x*x-y*y,2n*x*y,norm];
});
const unitValueNum = scaleNum**2n*planar*unit-cap*(2n*phaseDen+1n)*valueDen;
const unitValueDen = phaseDen**2n*valueDen*unit;
assert(10n**9n*unitValueNum >= 999701090n*unitValueDen, "unit planar value");
// Barycentric weights of zero in the three doubled-angle directions.
const triple = [0,58,110].map(j => directions[j]);
const weights = triple.map((v,i) => {
  const [x,y] = triple[(i+1)%3], [a,b] = triple[(i+2)%3];
  return v[2]*(x*b-y*a);
});
assert(sum(weights)>0n && weights.every(w => 25n*w>8n*sum(weights)), "isotropic triple");

const oldNum = 737877064811692678202731938521n, oldDen = 1194666547200000000000000000000n;
const gainDen = N*5000n*cap, gainNum = unit;
const num = oldNum*gainDen+oldDen*gainNum, divisor = oldDen*gainDen;
function gcd(a,b) { while (b) [a,b]=[b,a%b]; return a; }
const g = gcd(num,divisor), [lo,hi] = piInterval(), places = 10n**18n;
const lower = num*lo**2n*places/(divisor*10n**96n);
assert(lower === num*hi**2n*places/(divisor*10n**96n), "decimal floor");
// Pair projection partitions the triangle with area fractions 1/2, 1/4, 1/4.
const totalGain = 2n*chamberGains.parent+chamberGains.left+chamberGains.right;
const weightedDen = 4n*N*cap*oldDen, weightedNum = 4n*N*cap*oldNum+totalGain*oldDen;
const gw = gcd(weightedNum,weightedDen);
const weightedFloor = weightedNum*lo**2n*places/(weightedDen*10n**96n);
assert(weightedFloor === weightedNum*hi**2n*places/(weightedDen*10n**96n), "weighted decimal floor");
const targetNum = 123n, targetDen = 20n;
const missedWeightLimit = 879853n; // rounded upward in 10^-8
// If the area is below 123/20 then the frozen fraction is below 1 - B/(123/20).
assert((10n**8n-missedWeightLimit)*targetNum*oldDen*10n**96n <
  10n**8n*targetDen*oldNum*lo**2n, "missing diagonal weight at 6.15");
// Divide the larger, corrected action by the exhibited true comass.
assert(100000n*weightedNum*hi**2n*cap*valueDen < 609774n*weightedDen*10n**96n*unit*planar,
  "fixed-form rescaling ceiling");
console.log(JSON.stringify({phase_rectangles:results,certified_matrices:12,
  relaxed_parent_floor_1e9:String(relaxed*10n**9n/valueDen),
  planar_neighbor_floor_1e9:String(planar*10n**9n/valueDen),
  exact_pi_squared_factor:(num/g)+"/"+(divisor/g),
  area_floor:(lower/places)+"."+(lower%places).toString().padStart(18,"0"),
  retained_diagonal_fraction:"19/20",
  unit_neighbor_floor_1e9:String(10n**9n*unitValueNum/unitValueDen),
  isotropic_neighbor_indices:[0,58,110],
  isotropic_weights_floor_1e6:weights.map(w => String(10n**6n*w/sum(weights))),
  weighted_pi_squared_factor:(weightedNum/gw)+"/"+(weightedDen/gw),
  weighted_area_floor:(weightedFloor/places)+"."+(weightedFloor%places).toString().padStart(18,"0"),
  missed_weight_ceiling_in_1e8:String(missedWeightLimit)},null,2));
