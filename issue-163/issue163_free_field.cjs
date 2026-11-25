"use strict";

// Replay the finite multilevel calibration. All norm and action acceptance tests are integral.
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const zlib = require("node:zlib");
const crypto = require("node:crypto");
const {spawnSync} = require("node:child_process");
const {INPUT, piInterval, assert} = require("./issue163_fourier_caps.cjs");
const {loadField, ENDPOINT_FILE, ENDPOINT_STEPS, SIGMA, group} = require("./issue163_reweighted_field.cjs");

function readCorrection(file, length) {
  const record = JSON.parse(fs.readFileSync(file, "utf8"));
  const cap = record.budget_units_1e12;
  assert(Number.isSafeInteger(cap) && cap > 0 && cap <= 2e12, "invalid budget");
  const delta = Array(length).fill(0n);
  let last = -1;
  for (const [id, value] of record.master_delta) {
    assert(Number.isInteger(id) && id > last && id < length && Number.isSafeInteger(value) && value !== 0,
      "invalid master update");
    delta[id] = BigInt(value);
    last = id;
  }
  return {cap: BigInt(cap), delta, changed: record.master_delta.length};
}

function makeLevel(st, maps, base, delta, parent) {
  const {n, grid} = st, bins = grid.length - 1;
  const reps = maps("reps_" + n), variable = maps("class_variable_" + n);
  const sn = maps("class_scale_num_" + n), sd = maps("class_scale_den_" + n);
  const index = new Int32Array(n * bins * bins).fill(-1);
  const w = new BigInt64Array(variable.length);
  const endpoint = n === 112 ? new Map(ENDPOINT_STEPS) : new Map();
  const key = (k, a, b) => (k * bins + a) * bins + b;
  const scalar = Int32Array.from(grid.slice(0, -1), (x, a) => SIGMA[group((x + grid[a+1]) / 2)]);
  const valid = grid.slice(0, -1).map((x, a) => {
    for (let t = x; t < grid[a+1]; ++t) if (SIGMA[group(t + 0.5)] !== scalar[a]) return false;
    return true;
  });
  for (const a of st.boxes) assert(valid[a], "nonconstant slope on a reached terminal interval");
  const coarse = parent && grid.slice(0, -1).map((x, a) => {
    const p = parent.grid.findIndex((v, i, g) => v <= x && grid[a+1] <= g[i+1]);
    assert(p >= 0, "inconsistent grid nesting");
    return p;
  });
  const weightsN = maps("objective_num_" + n), weightsD = maps("objective_den_" + n);
  let action = 0n, original = 0n, inherited = 0, cells = 0;
  for (let j = 0; j < variable.length; ++j) {
    const id = variable[j];
    assert(id >= -1 && id < base.length && sd[j] > 0, "invalid variable or scale");
    const divisor = BigInt(sd[j]), multiplier = 8n * BigInt(sn[j]);
    const value = id < 0 ? 0n : (BigInt(base[id]) + delta[id]) * multiplier;
    const reference = id < 0 ? 0n : BigInt(base[id]) * multiplier;
    assert(value % divisor === 0n && reference % divisor === 0n, "coefficient denominator");
    const inc = BigInt(endpoint.get(j) || 0);
    const numerator = value/divisor + inc;
    assert(numerator >= -64000000000000n && numerator <= 64000000000000n, "coefficient range");
    w[j] = numerator;
    const [k, a, b] = reps.subarray(3*j, 3*j+3);
    const orbit = [[k,a,b], [k,b,a], [n-k,b,bins-1-a], [n-k,bins-1-a,b]];
    let weight = 0;
    for (const [l,x,y] of orbit) for (const [u,v] of [[x,y],[bins-1-x,bins-1-y]]) {
      const addr = key(l,u,v);
      if (index[addr] === j) continue;
      assert(index[addr] === -1, "intersecting coefficient orbits");
      index[addr] = j;
      ++cells;
      if (n === 112) {
        const diff = Math.abs(u-v), sum = Math.abs(u+v-n+1);
        assert(diff <= l && sum <= n-l, "outside boundary polygon");
        weight += (n-l) * (diff === l || sum === n-l ? 1 : 2);
      }
    }
    if (parent) {
      const edge = 56 - 2*112/n;
      const rim = z => grid[z+1] <= -edge || grid[z] >= edge;
      if (!rim(a) && !rim(b)) {
        let previous = 0n;
        if (k % 2 === 0) {
          const p = parent.index[parent.key(k/2, coarse[a], coarse[b])];
          assert(p >= 0, "missing parent class");
          previous = parent.w[p];
        }
        assert(2n * numerator === previous, "outside-band inheritance");
        ++inherited;
      }
    }
    if (n === 112) {
      assert(weight * weightsD[j] === 2 * weightsN[j], "boundary polygon weight");
      const cost = BigInt(weight) * BigInt(scalar[a]) * BigInt(scalar[b]);
      original += cost * (reference/divisor + inc);
      action += cost * numerator;
    }
  }
  if (n === 112) {
    assert(cells === 480704, "full positive-area pair domain");
    assert(original === 2475080672199852607407123768951328n, "reference boundary action");
  }
  return {grid, bins, w, index, scalar, key, action, inherited};
}

function run(command, args) {
  const result = spawnSync(command, args, {encoding:"utf8"});
  if (result.error || result.status !== 0)
    throw Error([command, result.error || "", result.stdout, result.stderr].join(" "));
  return result.stdout.trim();
}

function writeNativeInput(file, st, level, cap) {
  const header = Int32Array.of(st.n, level.bins, st.count, level.w.length);
  const diagonal = st.n === 112 ? st.diagonal : BigInt64Array.from(st.diagonal, v => 2n*BigInt(v));
  const fd = fs.openSync(file, "w");
  try {
    for (const a of [header, BigInt64Array.of(cap), st.boxes, level.index, level.w, level.scalar, diagonal])
      fs.writeFileSync(fd, Buffer.from(a.buffer, a.byteOffset, a.byteLength));
  } finally { fs.closeSync(fd); }
}

function gcd(a, b) { while (b) [a,b] = [b,a%b]; return a; }
function decimal(s, places) {
  const t = s.toString().padStart(places+1, "0");
  return t.slice(0,-places) + "." + t.slice(-places);
}

function replay(dir, correctionDir = __dirname) {
  assert(os.endianness() === "LE", "little-endian host required");
  const read = file => fs.readFileSync(path.join(dir, file));
  const raw = {endpoints:read(ENDPOINT_FILE)};
  for (const [k,[file]] of Object.entries(INPUT)) raw[k] = read(file);
  const io = {hash:data=>crypto.createHash("sha256").update(data).digest("hex"), utf8:b=>b.toString("utf8"),
    ungzip:zlib.gunzipSync, inflate:zlib.inflateRawSync};
  const {states, field, maps} = loadField(raw, io);
  assert(states.map(s=>s.count).join(",") === "53100,29410,14562,116986", "terminal coverage");
  const base = field("master_numerators");
  const {cap,delta,changed} = readCorrection(path.join(correctionDir, "issue163_free_coefficients.json"), base.length);
  const witnesses = zlib.gunzipSync(fs.readFileSync(path.join(correctionDir, "issue163_free_diagonals.bin.gz")));
  const temp = fs.mkdtempSync(path.join(os.tmpdir(), "issue163-gram-"));
  try {
    const exe = path.join(temp, "check"), src = path.join(__dirname, "issue163_free_psd.cpp");
    const cxx = process.env.CXX || "c++";
    try {
      run(cxx, ["-O3", "-std=c++17", "-fopenmp", src, "-o", exe]);
      run(exe, ["--check-runtime"]);
    } catch {
      run(cxx, ["-O3", "-std=c++17", src, "-o", exe]);
    }
    let offset = 0, parent = null;
    for (const st of states) {
      const level = makeLevel(st, maps, base, delta, parent);
      const count = witnesses.readUInt32LE(offset);
      const end = offset + 4 + 4*count*(1+st.n);
      assert(count <= st.count && end <= witnesses.length, "invalid level witness block");
      const input = path.join(temp,"matrix.bin"), cert = path.join(temp,"diagonals.bin");
      fs.writeFileSync(cert, witnesses.subarray(offset, end));
      writeNativeInput(input, st, level, cap);
      console.log(run(exe,[input,cert]) + ", " + level.inherited + " inherited classes checked");
      offset = end;
      parent = level;
    }
    assert(offset === witnesses.length, "extra witness block");
    const num = parent.action * 10n**12n, den = 112n**2n * 32000000000000n * 10n**16n * cap;
    assert(num > 0n, "nonpositive action");
    const unit = 10n**18n, common = gcd(num, den), factor = num*unit/den, piLow = piInterval()[0];
    return {changed_master_coefficients:changed, budget_units_1e12:String(cap), action_numerator:String(parent.action),
      exact_pi_squared_factor:String(num/common)+"/"+String(den/common), pi_squared_factor_floor:decimal(factor,18),
      area_lower_decimal:decimal(num*unit*piLow*piLow/(den*10n**96n),18)};
  } finally { fs.rmSync(temp, {recursive:true, force:true}); }
}

if (require.main === module) {
  if (!process.argv[2]) throw Error("Pass the directory of the five finite inputs.");
  console.log(JSON.stringify(replay(process.argv[2], process.argv[3]), null, 2));
}
module.exports = {replay, readCorrection, makeLevel};
