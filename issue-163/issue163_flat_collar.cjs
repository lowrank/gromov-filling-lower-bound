"use strict";

// Compare closed forms on explicit profile collars, using integer areas and field coefficients.
const path = require("node:path");
const zlib = require("node:zlib");
const {INPUT, npzReader, piInterval, assert} = require("./issue163_fourier_caps.cjs");
const {makeLevel, readCorrection} = require("./issue163_free_field.cjs");
const {pinned, HERM_DEN, BASE_NUM, BASE_DEN} = require("./issue163_midpoint.cjs");

const n = 112, N = BigInt(n), unit = 10n**12n, fieldDen = HERM_DEN/2n;
const dir = process.argv[2] || path.join(__dirname, "issue163_inputs");
const archive = name => npzReader(pinned(dir, ...INPUT[name]), zlib.inflateRawSync);
const maps = archive("maps"), base = archive("field")("master_numerators");
const data = "issue163_free_coefficients.json";
pinned(__dirname, data, "254eee5682f2dbd27510523684e67e3e2d88ea14344ba2836fe1be155041beea");
const {delta, cap} = readCorrection(path.join(__dirname, data), base.length);
const grid = Array.from({length:n+1}, (_,j) => j-n/2);
const level = makeLevel({n,grid,boxes:[]}, maps, base, delta, null);
assert(level.action*unit*BASE_DEN === 2n*N*N*fieldDen*cap*BASE_NUM, "old action and normalization");
const scalar = Array.from(level.scalar, BigInt);
function coefficient(gap, a, b) {
  const id = level.index[level.key(gap,a,b)];
  assert(id >= 0, "missing field cell");
  return level.w[id]*scalar[a]*scalar[b];
}

function gcd(a,b) { while (b) [a,b]=[b,a%b]; return a; }
const [piLo,piHi] = piInterval(), piScaleSq = 10n**96n;
function report(num, den) {
  assert(num > 0n && den > 0n, "positive ceiling");
  const g = gcd(num,den), places = 10n**9n, div = den*piScaleSq;
  const up = (num*piHi*piHi*places+div-1n)/div;
  assert(up === (num*piLo*piLo*places+div-1n)/div, "ambiguous decimal ceiling");
  return {factor_of_pi_squared:(num/g)+"/"+(den/g),
    upper:(up/places)+"."+(up%places).toString().padStart(9,"0")};
}

// Each vertex is an intersection of two integer lines with determinant at most 32.
let scale = 1n;
for (let i=2n; i<=32n; ++i) scale = scale/gcd(scale,i)*i;
function subdivide(polygon, a, b, c) {
  const values = polygon.map(([x,y]) => a*x+b*y-c*scale);
  if (values.every(v => v>=0n) || values.every(v => v<=0n)) return [polygon];
  const pieces = [[],[]];
  for (let i=0; i<polygon.length; ++i) {
    const j=(i+1)%polygon.length, p=polygon[i], q=polygon[j], u=values[i], v=values[j];
    if (u<=0n) pieces[0].push(p);
    if (u>=0n) pieces[1].push(p);
    if (u*v<0n) {
      const intersection = p.map((x,k) => {
        const increment = (q[k]-x)*u;
        assert(increment%(u-v) === 0n, "vertex denominator");
        return x+increment/(u-v);
      });
      for (const side of pieces) side.push(intersection);
    }
  }
  return pieces;
}

function mesh(k,width) {
  const end=BigInt(k)*scale;
  let polygons=[[[0n,0n],[end,end],[0n,end]]];
  for (let s=1; s<k; ++s) {
    const lines=[[1,1,2*s]];
    for (let t=0; t<=width; ++t) lines.push([width-t,t,s*width]);
    for (const line of lines) {
      const [a,b,c]=line.map(BigInt);
      polygons=polygons.flatMap(poly => subdivide(poly,a,b,c));
    }
  }
  return polygons;
}

function aligned(k) {
  const width=Math.ceil(k/2), w=BigInt(width), start=Math.floor((n+k-width)/2);
  const polygons=mesh(k,width);
  let totalArea2=0n, integral2=0n;
  for (const polygon of polygons) {
    let area2=0n, x=0n, y=0n;
    for (let i=0; i<polygon.length; ++i) {
      const [a,b]=polygon[i], [c,d]=polygon[(i+1)%polygon.length];
      x+=a; y+=b; area2+=a*d-b*c;
    }
    assert(area2>0n, "oriented polygon");
    totalArea2+=area2;
    const den=BigInt(polygon.length)*scale;
    const sample=Array.from({length:n}, (_,j) => {
      const ell=BigInt(Math.min(width,Math.max(0,j-start)));
      let a=w-ell,b=ell,offset=n-j;
      if (j<k && x+y>2n*BigInt(j)*den) { a=0n; b=-w; offset=n+j; }
      const val=BigInt(offset)*w*den+a*x+b*y;
      assert(val>0n && val<N*w*den && val%(w*den)!==0n, "centroid on scalar wall");
      return {a,b,bin:Number(val/(w*den))};
    });
    let density=0n;
    for (let i=0; i<n; ++i) for (let j=i+1; j<n; ++j) {
      const a=sample[i], b=sample[j], det=a.a*b.b-a.b*b.a;
      if (det!==0n) density+=coefficient(j-i,a.bin,b.bin)*det;
    }
    integral2+=area2*density;
  }
  const K=BigInt(k);
  assert(totalArea2===K*K*scale*scale, "triangle area");
  const meanNum=integral2*unit, meanDen=totalArea2*w*w*fieldDen*cap;
  assert(meanNum>0n && meanNum<meanDen, "mean normalized density");
  return {gap_width:k, polygons:polygons.length,
    ...report(BASE_NUM*N*meanDen+BASE_DEN*K*(meanDen-meanNum), BASE_DEN*N*meanDen)};
}

// Eight times the area in fine-grid units of a rectangle clipped to the pair polygon.
// Input coordinates are in half-grid units. The four removed corner pieces are disjoint.
const posSq = x => Math.max(0,x)**2;
function corner2(a,b,c,d,t) {
  return posSq(b+d-t)-posSq(a+d-t)-posSq(b+c-t)+posSq(a+c-t);
}
function clippedArea8(a,b,c,d,gap) {
  return 2*(b-a)*(d-c)-corner2(a,b,c,d,2*(n-gap))-corner2(-b,-a,-d,-c,2*(n-gap))
    -corner2(a,b,-d,-c,2*gap)-corner2(-b,-a,c,d,2*gap);
}

function rotating(k) {
  const preimage=grid.slice(0,-1).map(x => {
    const shift=x<0 ? -k : k;
    const clip=z => Math.min(n,Math.max(-n,z));
    return [clip(2*x+shift),clip(2*x+2+shift)];
  });
  let flux=0n;
  for (let gap=1; gap<n; ++gap) for (let a=0; a<n; ++a) for (let b=0; b<n; ++b) {
    const t=level.index[level.key(gap,a,b)];
    if (t<0 || level.w[t]===0n) continue;
    const area8=clippedArea8(...preimage[a],...preimage[b],gap);
    assert(Number.isInteger(area8) && 0<=area8 && area8<=8, "clipped pair area");
    flux+=BigInt((n-gap)*area8)*level.w[t]*scalar[a]*scalar[b];
  }
  const den=8n*N*N*fieldDen*cap;
  if (k===0) assert(flux*unit*BASE_DEN===den*BASE_NUM, "inner-loop flux at zero depth");
  return {gap_width:k, ...report(flux*unit+2n*BigInt(k)*den/N,den)};
}
const widths=[1,2,4,8], fixed=widths.map(aligned);
rotating(0);
const allAngles=widths.map(rotating);
assert(fixed.map(r=>r.upper).join() === "6.107523028,6.119731292,6.142450184,6.177826871", "aligned ceilings");
assert(allAngles.map(r=>r.upper).join() === "6.120073216,6.145244034,6.185707234,6.268961721", "rotation ceilings");
console.log(JSON.stringify({aligned:fixed, all_rotations:allAngles},null,2));
