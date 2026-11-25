"use strict";

const fs = require("node:fs");
const path = require("node:path");
const zlib = require("node:zlib");
const crypto = require("node:crypto");
const { INPUT, npzReader, piInterval, assert } = require("./issue163_fourier_caps.cjs");
const { ENDPOINT_STEPS, SIGMA, group } = require("./issue163_reweighted_field.cjs");

const N = 224, P = 112;
const U = 639413036587531299403539588646n;
const A = 2475080672199852607407123768951328n;
const lambdaNum = 50019n, lambdaDen = 50000n;
const abs = x => x < 0n ? -x : x;
const max = (x, y) => x > y ? x : y;
const key = (n, k, x, y) => (k*n+x)*n+y;

function integer(v) {
  assert(Number.isSafeInteger(v), "exact integer input");
  return BigInt(v);
}

function orbit(n, k, x, y) {
  const members = new Map();
  for (const [l, a, b] of [[k,x,y], [k,y,x], [n-k,y,n-1-x], [n-k,n-1-x,y]]) {
    for (const [c, d] of [[a,b], [n-1-a,n-1-b]]) members.set(key(n,l,c,d), [l,c,d]);
  }
  return members;
}

function archive(dir, id) {
  const [name, hash] = INPUT[id], buf = fs.readFileSync(path.join(dir,name));
  assert(crypto.createHash("sha256").update(buf).digest("hex") === hash, "input hash " + name);
  return npzReader(buf, zlib.inflateRawSync);
}

function parentField(dir) {
  const maps = archive(dir, "maps"), master = archive(dir, "field")("master_numerators");
  const ids = maps("class_variable_112"), num = maps("class_scale_num_112"), den = maps("class_scale_den_112");
  const reps = maps("reps_112"), an = maps("objective_num_112"), ad = maps("objective_den_112");
  const steps = new Map(ENDPOINT_STEPS), coeff = [], index = new Int32Array(P**3).fill(-1);
  let action = 0n;
  for (let o = 0; o < ids.length; o++) {
    const [k,a,b] = reps.subarray(3*o,3*o+3);
    const w = ids[o] < 0 ? 0n : 8n*integer(master[ids[o]])*integer(num[o]);
    assert(w % integer(den[o]) === 0n, "parent coefficient units");
    const s = integer(SIGMA[group(a-55.5)]) * integer(SIGMA[group(b-55.5)]);
    const scaled = (w / integer(den[o]) + integer(steps.get(o) || 0))*s;
    assert(2n*integer(an[o]) % integer(ad[o]) === 0n, "parent action units");
    action += (2n*integer(an[o])/integer(ad[o]))*scaled;
    coeff.push(2n*scaled); // U times the half-weight on one child parity.
    for (const id of orbit(P,k,a,b).keys()) {
      assert(index[id] === -1, "disjoint parent classes");
      index[id] = o;
    }
  }
  assert(action === A, "signed parent boundary action");
  return (k, a, b) => {
    if (k % 2) return 0n;
    const o = index[key(P,k/2,a>>1,b>>1)];
    assert(o >= 0, "compatible parent cell");
    return coeff[o];
  };
}

function endpointClasses() {
  const index = new Map(), weights = [];
  for (let k = 1; k <= P; k++) for (let x = 0; x <= 1; x++) for (let y = 0; y < N; y++) {
    if (Math.abs(x-y) > k || Math.abs(x+y-N+1) > N-k || index.has(key(N,k,x,y))) continue;
    let weight = 0;
    for (const [id,[l,a,b]] of orbit(N,k,x,y)) {
      assert(!index.has(id), "disjoint endpoint classes");
      index.set(id, weights.length);
      const boundary = Math.abs(a-b) === l || Math.abs(a+b-N+1) === N-l;
      weight += (N-l)*(boundary ? 1 : 2);
    }
    weights.push(integer(weight));
  }
  assert(weights.length === 666, "all endpoint classes");
  return {index, weights};
}

function profile(tag) {
  assert(["A","B","central"].includes(tag), "profile name");
  const row = Array.from({length:N}, (_,i) => {
    if (tag === "central") return i <= P ? P : P-1;
    if (tag === "A") return i === 0 ? 0 : i-1;
    return i < 4 ? 1 : i-2;
  });
  // Midpoints satisfy the two angular inequalities. A slight contraction
  // towards zero makes both strict and preserves all the open cell labels.
  for (let i = 0; i < N; i++) for (let j = i+1; j < N; j++) {
    assert(Math.abs(row[i]-row[j]) <= j-i && Math.abs(row[i]+row[j]-N+1) <= N-j+i, "admissible row");
  }
  return row;
}

function verifyScale(test, J, parent) {
  const row = profile("central"), z = test.map(pair => pair.map(integer));
  assert(z.length === N && z.every(p => p.length === 2 && p[0]**2n+p[1]**2n <= J*J), "central unit disk");
  let base = 0n;
  for (let i = 0; i < N; i++) for (let j = i+1; j < N; j++) {
    const det = z[i][0]*z[j][1]-z[i][1]*z[j][0];
    assert(det >= 0n, "nonnegative Fourier evaluation");
    base += det*parent(j-i,row[i],row[j]);
  }
  assert(lambdaNum*base > lambdaDen*U*J*J, "central bound on parent scale");
}

function groupedRow(row, sectors) {
  assert(Number.isInteger(sectors) && sectors >= 1 && sectors <= P, "sector count");
  const labels = row.map((a,i) => a < 2 || a >= N-2 ? N+i : 2*Math.floor(sectors*i/N)+(i%2));
  const unique = [...new Set(labels)].sort((a,b) => a-b);
  return {groups:labels.map(k => unique.indexOf(k)), size:unique.length};
}

function integrate(test, mode, parent, classes, slopes, seen) {
  assert(test.profile === "A" || test.profile === "B", "outer test");
  const row = profile(test.profile), {groups,size} = groupedRow(row,test.sectors);
  const X = test.real.map(v => v.map(integer)), Y = test.imag.map(v => v.map(integer)), rank = X[0].length;
  assert(rank > 0 && X.length === size && Y.length === size && X.concat(Y).every(v => v.length === rank), "witness dimensions");
  const norms = X.map((v,i) => v.map((x,k) => x*x+Y[i][k]**2n));
  const mass = mode === "psd" ? norms.reduce((m,v) => max(m,v.reduce((s,a) => s+a,0n)),0n)
    : X[0].reduce((s,_,k) => s+norms.reduce((m,v) => max(m,v[k]),0n),0n);
  const currents = X.map((v,g) => X.map((w,h) => v.reduce((s,x,k) => s+x*Y[h][k]-Y[g][k]*w[k],0n)));
  let base = 0n;
  for (let i = 0; i < N; i++) for (let j = i+1; j < N; j++) {
    const det = currents[groups[i]][groups[j]], w = parent(j-i,row[i],row[j]);
    base += w*det;
    const o = classes.index.get(key(N,j-i,row[i],row[j]));
    if (o !== undefined) {
      // Single-edge planar tests imply |x_o| <= 1 + lambda |W0_ij|.
      assert(10n*lambdaNum*abs(w) <= lambdaDen*U, "endpoint coefficient range");
      seen.add(o);
      slopes[o] += det;
    }
  }
  return {mass, base};
}

function upper(mode, tests, J, parent, classes) {
  const slopes = classes.weights.map(() => 0n), seen = new Set();
  let mass = 0n, base = 0n;
  for (const test of tests) {
    const v = integrate(test,mode,parent,classes,slopes,seen);
    mass += v.mass;
    base += v.base;
  }
  assert(seen.size === classes.weights.length, "single-edge tests cover the variables");
  const p2 = BigInt(P)**2n, wd = 2n*BigInt(N)**2n, j2 = J*J;
  const residual = slopes.reduce((s,g,o) => s+abs(classes.weights[o]*j2-wd*g),0n);
  const gap = max(0n,2n*A*j2-p2*base);
  // Common denominator for m + (50019/50000)(alpha-b)_+ + (11/10) sum |omega-g|.
  const den = 10n*lambdaDen*p2*U*wd*j2;
  const num = mass*(den/j2) + lambdaNum*gap*10n*wd + 11n*residual*lambdaDen*p2*U;
  const pi = piInterval()[1], scale = 10n**96n;
  const digits = 10n**12n;
  const ceil = (a,b) => (a+b-1n)/b;
  const finite = ceil(digits*num*pi*pi,den*scale);
  // The previously fixed Fourier form contributes less than 0.0000063
  // per unit lambda. Its published action and endpoint support are used here.
  const fourier = ceil(digits*63n*lambdaNum,10n**7n*lambdaDen);
  return {tests:tests.length, columns:tests.reduce((s,t) => s+t.real[0].length,0),
    finite_upper_1e12:String(finite), with_fixed_fourier_upper_1e12:String(finite+fourier)};
}

module.exports = { parentField, U };

if (require.main === module) {
  const dir = process.argv[2];
  if (!dir) throw Error("Pass the finite certificate directory.");
  const data = JSON.parse(zlib.gunzipSync(fs.readFileSync(path.join(__dirname,"issue163_signed_tests.json.gz"))));
  const parent = parentField(dir), classes = endpointClasses(), J = integer(data.denominator);
  assert(J > 0n, "rational witness denominator");
  verifyScale(data.central,J,parent);
  const report = {};
  for (const mode of ["psd","planar"]) report[mode] = upper(mode,data[mode],J,parent,classes);
  assert(BigInt(report.psd.with_fixed_fourier_upper_1e12) < 6140000000000n, "PSD ceiling below 6.14");
  assert(BigInt(report.planar.with_fixed_fourier_upper_1e12) < 6150000000000n, "planar ceiling below 6.15");
  console.log(JSON.stringify(report,null,2));
}
