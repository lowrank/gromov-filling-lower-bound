"use strict";

// Two matrix evaluations and a two-equation dual certificate, with no optimization.
const path = require("node:path");
const {assert, piInterval} = require("./issue163_fourier_caps.cjs");
const {loadProfile, HERM_DEN: H, pinned} = require("./issue163_midpoint.cjs");
const record = JSON.parse(pinned(__dirname, "issue163_planar_witness.json",
  "c68acffd8bc66d90e359550a783cac92c0b31fe7817577a374075167d36350e9"));
const folder = path.join(__dirname, "issue163_inputs");
const n = 112, G = 100000000n, N = BigInt(n), budgetScale = 10n**12n;
const cap = 999999900000n, common = N*H*G**2n*cap;
const det = ([x,y],[u,v]) => x*v-y*u;
const left = [6500,-2040,-800,-200,0,0,0,-900,...Array(12).fill(-60),...Array(35).fill(-4),0];
const coefficients = left.concat(left.slice(0,-1).reverse()).map(BigInt);

function evaluate(bins, rows, highLast) {
  const data = loadProfile(folder, bins);
  assert(data.cap === cap && rows.every(([x,y]) => x*x+y*y <= G*G), "gradient and cap bounds");
  let raw = 0n, quarter = 0n;
  for (let i = 0; i < n; i++) {
    for (let j = i+1; j < n; j++) raw += 2n*data.w[i][j]*det(rows[i],rows[j]);
    quarter += (i<n/2 ? 1n : -1n)*det(rows[i], rows[(i+n/2)%n]);
  }
  if (highLast) {
    assert(raw*10n**9n/(H*G**2n) === 999701031n, "published neighboring cell");
    // The only high signed anchor is -1, and the bisected tent is inactive.
    for (let j = 0; j < n-1; j++)
      raw -= H/1000000n*coefficients[j]*det(rows[n-1],rows[j]);
  }
  return {W:raw*budgetScale*N, Q:quarter*H*cap};
}

const profile = Array.from({length:n}, (_,j) => 2000*(55-j)+2*j-55);
const neighbor = evaluate(profile.map(x => Math.floor(x/2000+56)),
  record.neighbor_planar_vectors.map(row => row.map(BigInt)), true);
const first = Array.from({length:n/2}, (_,j) => {
  const t = j*Math.PI/n;
  // Trigonometry proposes integers. Every subsequent bound is an integer comparison.
  return [Math.cos(t),Math.sin(t)].map(x => BigInt(Math.round((Number(G)-2)*x)));
});
const center = evaluate(Array.from({length:n}, (_,j) => j<=56 ? 56 : 55),
  first.concat(first.map(([x,y]) => [-y,x])), false);
assert(center.W*100000n > 99992n*common && center.Q*100000n > 99999n*common, "central test");
assert(neighbor.W*100000n > 99922n*common, "single-anchor correction");

const bNum = 2213775623134282058736195815563n, bDen = 3583999641600000000000000000000n;
const determinant = neighbor.W*center.Q-center.W*neighbor.Q;
const weightNeighbor = common*(2n*bNum*center.Q-bDen*center.W);
const weightCenter = common*(bDen*neighbor.W-2n*bNum*neighbor.Q);
const denominator = 2n*bDen*determinant;
assert(determinant>0n && weightNeighbor>0n && weightCenter>0n, "positive dual weights");
assert(bDen*(weightNeighbor*neighbor.W+weightCenter*center.W) === bNum*denominator*common,
  "original action moment");
assert(2n*(weightNeighbor*neighbor.Q+weightCenter*center.Q) === denominator*common,
  "quarter-turn action moment");
const [pLo,pHi] = piInterval(), weights = weightNeighbor+weightCenter;
const decimalScale = 10n**48n;
assert(100000n*pHi**2n*weights < 609878n*denominator*decimalScale**2n, "two-test ceiling");
const lowerFloor = 10n**8n*pLo**2n*weights/(denominator*decimalScale**2n);
const upperFloor = 10n**8n*pHi**2n*weights/(denominator*decimalScale**2n);
assert(lowerFloor === upperFloor, "decimal floor");
console.log("Signed two-field family: two-test ceiling below 6.09878; normalized dual mass floor in 1e-8:",
  String(lowerFloor));
