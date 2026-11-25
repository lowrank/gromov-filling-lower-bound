"use strict";

// Check both local improvements over the Gaussian integers.
const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const zlib = require("node:zlib");
const {INPUT, npzReader, piInterval, assert} = require("./issue163_fourier_caps.cjs");
const {SIGMA, ENDPOINT_STEPS, group} = require("./issue163_reweighted_field.cjs");

const N = 112;
const UNIT = 10n ** 12n;
const HERM_DEN = 32n * UNIT * 10n ** 16n;
const BASE_NUM = 316186938521718142086885116509n;
const BASE_DEN = 511999948800000000000000000000n;

function pinned(dir, name, expected) {
  const bytes = fs.readFileSync(path.join(dir, name));
  assert(crypto.createHash("sha256").update(bytes).digest("hex") === expected, "hash of " + name);
  return bytes;
}

function key(k, a, b) {
  return (k * N + a) * N + b;
}

// Index just the pair cells of the one decreasing bin profile.
function cornerField(inputDir, correction) {
  const archive = name => npzReader(pinned(inputDir, ...INPUT[name]), zlib.inflateRawSync);
  const maps = archive("maps"), master = archive("field")("master_numerators");
  const reps = maps("reps_112"), ids = maps("class_variable_112");
  const sn = maps("class_scale_num_112"), sd = maps("class_scale_den_112");
  const delta = new Map(correction.master_delta), endpoint = new Map(ENDPOINT_STEPS);
  const cells = new Map();
  for (let i = 0; i < N; ++i)
    for (let j = i+1; j < N; ++j) cells.set(key(j-i,N-1-i,N-1-j), null);
  for (let o = 0; o < ids.length; ++o) {
    const k = reps[3*o], a = reps[3*o+1], b = reps[3*o+2];
    const orbit = [[k,a,b], [k,b,a], [N-k,b,N-1-a], [N-k,N-1-a,b]];
    for (const [s,x,y] of orbit) for (const [u,v] of [[x,y],[N-1-x,N-1-y]]) {
      const addr = key(s,u,v);
      if (!cells.has(addr)) continue;
      const id = ids[o], den = BigInt(sd[o]);
      const num = id < 0 ? 0n : (BigInt(master[id]) + BigInt(delta.get(id) || 0)) * 8n * BigInt(sn[o]);
      assert(den > 0n && num % den === 0n, "pair coefficient scale");
      const value = num/den + BigInt(endpoint.get(o) || 0);
      const prev = cells.get(addr);
      assert(prev === null || prev === value, "inconsistent pair orbit");
      cells.set(addr, value);
    }
  }
  const w = Array.from({length:N}, () => Array(N).fill(0n));
  const sigma = Array.from({length:N}, (_,i) => BigInt(SIGMA[group((N-1)/2-i)]));
  for (let i = 0; i < N; ++i) for (let j = i+1; j < N; ++j) {
    const cell = cells.get(key(j-i,N-1-i,N-1-j));
    assert(typeof cell === "bigint", "missing corner coefficient");
    w[i][j] = cell * sigma[i] * sigma[j]; // HERM_DEN times W_ij/2
    w[j][i] = -w[i][j];
  }
  for (let i = 0; i < N; ++i) for (let j = 0; j < N; ++j)
    assert(w[N-1-i][N-1-j] === -w[i][j], "corner reflection");
  return w;
}

function integers(values, length) {
  assert(Array.isArray(values) && values.length === length && values.every(Number.isSafeInteger),
    "invalid integer witness array");
  return values.map(BigInt);
}

function mirror(half) {
  const v = integers(half, N/2);
  return v.concat(v.slice().reverse());
}

// Fraction-free Hermitian elimination. After each step the next pivot is the
// next leading principal minor. Only the lower triangle is stored.
function positiveDefinite(re, im) {
  let previous = 1n;
  for (let k = 0; k < re.length; ++k) {
    const p = re[k][k];
    assert(im[k][k] === 0n && p > 0n, "nonpositive leading minor " + (k+1));
    for (let i = k+1; i < re.length; ++i) for (let j = k+1; j <= i; ++j) {
      const a = re[i][k], b = im[i][k], c = re[j][k], d = im[j][k];
      const s = p*re[i][j] - a*c - b*d;
      const t = p*im[i][j] - b*c + a*d;
      assert(s % previous === 0n && t % previous === 0n, "non-exact Bareiss division");
      re[i][j] = s/previous;
      im[i][j] = t/previous;
    }
    previous = p;
  }
}

function gcd(a,b) {
  while (b) [a,b] = [b,a%b];
  return a;
}

function areaFloor(num,den) {
  const [lo,hi] = piInterval(), scale = 10n**18n, divisor = den*10n**96n;
  const x = num*lo*lo*scale/divisor;
  assert(x === num*hi*hi*scale/divisor, "ambiguous decimal floor");
  return (x/scale) + "." + (x%scale).toString().padStart(18,"0");
}

const sum = values => values.reduce((total,x) => total+x,0n);

function actionReport(gainNum, gainDen) {
  assert(gainNum > 0n, "no action gain");
  const num = BASE_NUM*gainDen + gainNum*BASE_DEN, combinedDen = BASE_DEN*gainDen;
  const h = gcd(num,combinedDen), q = gcd(gainNum,gainDen);
  return {gain_pi_squared_factor:(gainNum/q)+"/"+(gainDen/q), area_gain_floor:areaFloor(gainNum,gainDen),
    exact_pi_squared_factor:(num/h)+"/"+(combinedDen/h), area_floor:areaFloor(num,combinedDen)};
}

function checkChamber(d, im, den, cap) {
  const trace = sum(d);
  assert(trace*UNIT <= den*cap, "local trace exceeds the original budget");
  const re = d.map((x,i) => [...Array(i).fill(0n),x*(HERM_DEN/den)]);
  positiveDefinite(re,im);
  return trace+"/"+den;
}

function bisection(w, record, den, cap) {
  const parent = mirror(record.parent_half), child = integers(record.child,N);
  const unit = HERM_DEN/(2n*den), traces = [];
  for (const [name,row] of [["parent_diagonal",null],["left_diagonal",0],["right_diagonal",N-1]]) {
    const d = integers(record[name],N), im = d.map((_,i) => Array(i+1).fill(0n));
    assert(d.every(x => 16n*BigInt(N)*x*UNIT >= cap*den), "local normalized diagonal floor");
    for (let i = 1; i < N; ++i) for (let j = 0; j < i; ++j) {
      let delta = j === 0 ? -parent[i] : 0n;
      if (row === 0 && j === 0) delta -= child[i];
      if (row === N-1 && i === N-1) delta -= child[j];
      im[i][j] = w[i][j] + unit*delta;
    }
    traces.push(checkChamber(d,im,den,cap));
  }
  const gainNum = (2n*sum(parent)+sum(child))*UNIT, gainDen = 4n*BigInt(N)*den*cap;
  return {positive_leading_minors:[N,N,N], normalized_diagonal_floor:"1/(16n)",
    traces, parent_sum:String(sum(parent)), child_sum:String(sum(child)),
    ...actionReport(gainNum,gainDen)};
}

function loadCorner(inputDir) {
  const correction = JSON.parse(pinned(__dirname, "issue163_free_coefficients.json",
    "254eee5682f2dbd27510523684e67e3e2d88ea14344ba2836fe1be155041beea"));
  const cap = BigInt(correction.budget_units_1e12);
  assert(cap === 999999900000n, "previous comass budget");
  return {w:cornerField(inputDir, correction), cap};
}

function verify(inputDir, witnessFile) {
  const {w,cap} = loadCorner(inputDir);
  const record = JSON.parse(fs.readFileSync(witnessFile, "utf8"));
  assert(Number.isSafeInteger(record.denominator) && record.denominator > 0, "witness denominator");
  const den = BigInt(record.denominator);
  assert(HERM_DEN % (2n*den) === 0n, "incompatible units");
  const g = mirror(record.cell_tent_half), v = mirror(record.distance_tent_half);
  const d = integers(record.diagonal,N+1);
  const im = d.map((_,i) => Array(i+1).fill(0n));
  const unit = HERM_DEN/(2n*den);
  for (let i = 1; i < N; ++i) for (let j = 0; j < i; ++j)
    im[i][j] = w[i][j] - (j === 0 ? unit*g[i] : 0n);
  for (let i = 0; i < N; ++i) im[N][i] = unit*v[i];
  const trace = checkChamber(d,im,den,cap);
  const gainNum = (sum(g)+sum(v))*UNIT, gainDen = 2n*BigInt(N)*den*cap;
  return {midpoint:{positive_leading_minors:N+1, trace, cell_tent_sum:String(sum(g)),
    distance_tent_sum:String(sum(v)), ...actionReport(gainNum,gainDen)},
    bisected_midpoint:bisection(w,record.bisection,den,cap)};
}

if (require.main === module) {
  const dir = process.argv[2] || path.join(__dirname,"issue163_inputs");
  const file = process.argv[3] || path.join(__dirname,"issue163_midpoint_witness.json");
  console.log(JSON.stringify(verify(dir,file),null,2));
}

module.exports = {loadCorner, pinned, HERM_DEN, BASE_NUM, BASE_DEN};
