"use strict";

const { assert, piInterval } = require("./issue163_fourier_caps.cjs");
const { cosPi, S } = require("./issue163_hemisphere_cap.cjs");
const K = 1536, sectors = 16, unit = 100000000n;
const min = (a,b) => a < b ? a : b;
const max = (a,b) => a > b ? a : b;
const ceil = (a,b) => (a+b-1n)/b; // Nonnegative arguments.
const sourcePi = piInterval();
const pi = [sourcePi[0]/10n**16n,ceil(sourcePi[1],10n**16n)];

function rootFloor(n) {
  if (n === 0n) return 0n;
  let a = 1n << BigInt(Math.ceil(n.toString(2).length/2));
  for (;;) {
    const b = (a+n/a)/2n;
    if (b >= a) return a;
    a = b;
  }
}

function trig(j,d) {
  const clamp = v => [max(0n,v[0]),min(S,v[1])];
  return {c:clamp(cosPi(j,d)), s:clamp(cosPi(d/2-j,d))};
}

function height({c,s},j) {
  if (j === 0) return [S,S];
  if (j === K) return [0n,0n];
  // z = pi*c / sqrt(pi^2*c^2+16*s^2).
  const p = pi[0]*c[0], q = 4n*S*s[1], P = pi[1]*c[1], Q = 4n*S*s[0];
  return [rootFloor(S*S*p*p/(p*p+q*q)),1n+rootFloor(S*S*P*P/(P*P+Q*Q))];
}

function direction(cosA,angle) {
  const x = cosA*Math.cos(angle), y = Math.sin(angle), len = Math.hypot(x,y);
  const a = BigInt(Math.floor(Number(unit-2n)*x/len)), b = BigInt(Math.floor(Number(unit-2n)*y/len));
  assert(a >= 0n && b >= 0n && a*a+b*b <= unit*unit, "rational planar test");
  return [a,b];
}

function detLower(j,cosA) {
  // On each of two angular intervals use 'sectors' constant unit-disk
  // gradients per quadrant. The two quadrant moments have elementary integrals.
  const den = 2*K*sectors, proposalC = Math.cos(Math.PI*j/(2*K));
  let mx = 0n, my = 0n;
  for (const core of [true,false]) {
    const offset = core ? 0 : (K-j)*sectors, width = core ? K-j : j;
    if (width === 0) continue;
    let a = trig(offset,den);
    for (let l = 0; l < sectors; l++) {
      const p = offset+l*width, b = trig(p+width,den);
      const [ux,uy] = direction(proposalC,(p+width/2)*Math.PI/den);
      let cx, sy;
      if (core) {
        cx = max(0n,b.s[0]-a.s[1])*S**3n/cosA[1]**3n;
        sy = max(0n,a.c[0]-b.c[1])*S**3n/cosA[1]**3n;
      } else {
        assert(a.s[0] > 0n, "positive tail endpoint");
        cx = max(0n,S**3n/a.s[1]**2n-ceil(S**3n,b.s[0]**2n))/2n;
        sy = max(0n,S*a.c[0]/a.s[1]-ceil(S*b.c[1],b.s[0]));
      }
      mx += ux*cx;
      my += uy*sy;
      a = b;
    }
  }
  return 16n*S*mx*my/(pi[1]**2n*unit**2n);
}

let saving = 0n;
const angles = Array.from({length:K+1}, (_,j) => trig(j,2*K));
const heights = angles.map(height);
for (let j = 0; j < K; j++) {
  const width = max(0n,heights[j][0]-heights[j+1][1]);
  const D = detLower(j,angles[j].c), z = heights[j+1][0];
  const factor = D*z**3n/S**3n;
  if (factor > S) saving += width*(factor-S)/factor;
}
const areaUpper = ceil(2n*pi[1]*(S-saving)*10n**12n,S*S);
assert(areaUpper < 6150000000000n, "single-map action below 6.15");

// A second family starts at the centered three-wave and ends at the
// boundary. Its quadrant profile is max(A-t,t-pi/2).
const bandCount = 768, bins = 96, denom = 2*bins*bins;
assert(bins*bins % bandCount === 0 && bandCount % 3 === 0, "common angular units");
const step = bins*bins/bandCount;
const cosCache = new Map();
function upperCos(k) {
  if (!cosCache.has(k)) cosCache.set(k,cosPi(k,denom)[1]);
  return cosCache.get(k);
}
function foldedHeight(j) {
  if (j === bandCount/3) return [S,S];
  if (j === bandCount) return [0n,0n];
  const {c,s} = trig(j,2*bandCount);
  const p = pi[0]*c[0], q = 2n*S*(2n*s[1]-S);
  const P = pi[1]*c[1], Q = 2n*S*(2n*s[0]-S);
  assert(Q > 0n, "positive folded radius");
  return [rootFloor(S*S*p*p/(p*p+q*q)),1n+rootFloor(S*S*P*P/(P*P+Q*Q))];
}
const mesh = Array.from({length:bins+1}, (_,l) => trig(l*l,denom));
let foldedSaving = 0n;
for (let j = bandCount/3; j < bandCount; j++) {
  const z = foldedHeight(j+1)[0], width = max(0n,foldedHeight(j)[0]-foldedHeight(j+1)[1]);
  const proposalC = Math.cos(Math.PI*(j+0.5)/(2*bandCount));
  let mx = 0n, my = 0n;
  for (let l = 0; l < bins; l++) {
    const a = l*l, b = (l+1)**2;
    const fmin = Math.max(j*step-b,a-denom/2);
    const fmax = Math.max((j+1)*step-a,b-denom/2);
    const c = upperCos(Math.max(0,fmin,-fmax));
    const [x,y] = direction(proposalC,Math.PI*(a+b)/(2*denom));
    mx += x*max(0n,mesh[l+1].s[0]-mesh[l].s[1])*S**3n/(c**3n);
    my += y*max(0n,mesh[l].c[0]-mesh[l+1].c[1])*S**3n/(c**3n);
  }
  const D = 16n*S*mx*my/(pi[1]**2n*unit**2n), factor = D*z**3n/S**3n;
  if (factor > S) foldedSaving += width*(factor-S)/factor;
}
const foldedUpper = ceil(2n*pi[1]*(S-foldedSaving)*10n**12n,S*S);
assert(foldedUpper < 6000000000000n, "folded profile ceiling below six");

// Upper bound for the *full* independent-gradient norm on a folded profile,
// needed for the third-harmonic correction. A fixed ellipse in each amplitude
// interval gives an upper bound for every planar gradient at once.
function modelNormUpper(model) {
  const bands = 128, angular = 256, d = 3*2**18;
  const t = Array.from({length:angular+1}, (_,l) => (d/(2*angular**2))*l*l);
  const trigCache = new Map();
  function angle(k) {
    if (!trigCache.has(k)) trigCache.set(k,trig(k,d));
    return trigCache.get(k);
  }
  let worst = 0n, last = 0;
  for (let depth = 0; depth < 9; depth++) {
    const span = model === "folded" ? 3 : 2;
    const dx = d/(span*bands*2**(depth+1));
    for (let j = 2*bands; j > bands; j--) {
      const a0 = d/2-j*dx, a1 = a0+dx;
      last = a1;
      const {c,s} = angle(a0), ellipse = c[0];
      const P = pi[1]*c[1];
      const Q = model === "folded" ? 2n*S*max(0n,2n*s[0]-S) : 4n*S*s[0];
      const zUpper = min(S,1n+rootFloor(S*S*P*P/(P*P+Q*Q)));
      let integral = 0n;
      for (let l = 0; l < angular; l++) {
        const lo = Math.max(a0-t[l+1],t[l]-d/2), hi = Math.max(a1-t[l],t[l+1]-d/2);
        const magnitude = model === "folded" ? Math.max(Math.abs(lo),Math.abs(hi)) : Math.min(a1,d/2-t[l]);
        const q = angle(magnitude).c[0];
        const right = angle(t[l+1]);
        const norm = 1n+rootFloor(ceil((ellipse*right.c[1])**2n,(S*S))+right.s[1]**2n);
        integral += ceil(BigInt(t[l+1]-t[l])*S**3n*norm,BigInt(d)*q**3n);
      }
      // integral/S bounds (1/pi) integral sec^3(f) |diag(ellipse/S,1)e_t| dt in one quadrant.
      const val = ceil(4n*integral**2n*zUpper**3n*10n**12n,ellipse*S**4n);
      worst = max(worst,val);
    }
  }
  const end = angle(last);
  const radiusNumerator = model === "folded" ? 2n*S*(2n*end.s[0]-S) : 4n*S*end.s[0];
  assert(radiusNumerator > 100n*pi[1]*end.c[1], "radius coverage through 100");
  assert(worst <= 1500000000000n, "two-thirds correction has norm at most one");
  return worst;
}
const foldNorm = modelNormUpper("folded"), clipNorm = modelNormUpper("clipped");
console.log(JSON.stringify({clipped_intervals:K,clipped_sectors_per_quadrant:2*sectors,
  clipped_upper_1e12:String(areaUpper),folded_intervals:bandCount*2/3,
  folded_sectors_per_quadrant:bins,folded_upper_1e12:String(foldedUpper),
  folded_uncorrected_norm_upper_through_radius_100_1e12:String(foldNorm),
  clipped_uncorrected_norm_upper_through_radius_100_1e12:String(clipNorm)},null,2));
