"use strict";

const {assert, piInterval} = require("./issue163_fourier_caps.cjs");
const {S, cosPi} = require("./issue163_hemisphere_cap.cjs");
const [piLo,piHi] = piInterval(), P = 10n**48n, digits = 10n**9n;
const ceil = (x,y) => (x+y-1n)/y;

function disk(n) {
  const N = BigInt(n), h = Math.PI/n, R = h/2;
  const cosLo = cosPi(1,n)[0], sinHi = cosPi(n-2,2*n)[1];
  // Area <= 2 pi - (2 pi^2/n)(1/2 - pi/8 - pi tan(h)^2/24).
  const margin = 12n*P*cosLo**2n - piHi*(3n*cosLo**2n+sinHi**2n);
  const den = 24n*P*cosLo**2n;
  assert(margin > 0n, "positive area removed");
  const areaUpper = ceil(digits*(2n*piHi*N*P*den-2n*piLo**2n*margin),N*P**2n*den);

  // Independently enclose the two inverse angles in the meridian length.
  const units = 1e12, T = BigInt(units);
  const a = Math.floor(units*Math.asin(Math.tan(R))/Math.PI)-1;
  const d = Math.ceil(units*Math.acos(Math.sqrt(Math.cos(h)))/Math.PI)+1;
  assert(a > 0 && d > 0 && a < units/2 && d < units/2, "acute meridian angles");
  const sinRLo = cosPi(n-1,2*n)[0], cosRHi = cosPi(1,2*n)[1];
  assert(cosPi(units/2-a,units)[1]*cosRHi < sinRLo*S, "lower latitude");
  assert(cosPi(d,units)[1]**2n < cosLo*S, "upper endpoint distance");
  const rootDen = 1000000n, rootHi = 1414214n;
  assert(rootHi**2n > 2n*rootDen**2n && BigInt(d)*2n*N > T, "square-root bound");
  const delta = BigInt(a)*rootDen*2n*N - rootHi*(BigInt(d)*2n*N-T);
  assert(delta > 0n, "positive shortcut");
  const shortLower = digits*2n*piLo*delta/(P*T*rootDen*2n*N);

  // The quadrature is illustrative. The two inequalities above use directed integers.
  const parts = 256;
  let total = 0;
  for (let i=1; i<parts; ++i) {
    const t = Math.PI*i/parts, s = R*(1-Math.cos(t));
    const height = Math.sqrt(Math.tan(s)*Math.tan(h-s));
    const angle = 2*Math.asin(Math.sqrt(Math.sin((h+s)/2)*Math.sin((h-s)/2)/Math.cos(s)));
    total += (i%2 ? 4 : 2)*R*Math.sin(t)*(height-angle+h-s);
  }
  return {anchor_pairs:n, limiting_area_approx:2*Math.PI-2*n*total*Math.PI/(3*parts),
    limiting_area_upper_in_billionths:Number(areaUpper),
    limiting_meridian_shortening_lower_in_billionths:Number(shortLower)};
}
const results = [14,15,56,112].map(disk);
assert(results[1].limiting_area_upper_in_billionths < 6150000000, "fifteen tests allow area below 6.15");
assert(results[3].limiting_area_upper_in_billionths < 6264300000 &&
  results[3].limiting_meridian_shortening_lower_in_billionths > 11600000, "112-pair example");
console.log(JSON.stringify(results,null,2));
