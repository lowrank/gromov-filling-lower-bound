"use strict";

const path=require("node:path");
const {assert,piInterval}=require("./issue163_fourier_caps.cjs");
const {loadProfile,HERM_DEN:H,BASE_NUM,BASE_DEN}=require("./issue163_midpoint.cjs");
const {cosPi,S}=require("./issue163_hemisphere_cap.cjs");

const input=process.argv[2] || path.join(__dirname,"issue163_inputs");
const n=112, N=BigInt(n), capNum=9999999n, capDen=10000000n;
const [piLo,piHi]=piInterval(), piUnits=10n**96n;
const digits=10n**12n, micro=1000000n;
const ceil=(a,b)=>a/b+(a%b>0n?1n:0n);
const out=v=>(v/digits)+"."+(v%digits).toString().padStart(12,"0");
const record=require("./issue163_planar_witness.json");
const unit=BigInt(record.phase_denominator), phases=record.neighbor_planar_vectors.map(p=>p.map(BigInt));
assert(phases.length===n && phases.every(([x,y])=>x*x+y*y<=unit*unit),"planar disks");
const z=phases.concat(phases.map(([x,y])=>[-x,-y]));
const det=(a,b)=>a[0]*b[1]-a[1]*b[0];
const wedge=Array.from({length:n},(_,j)=>z.map((v,a)=>det(v,z[(a+j)%(2*n)])));

// P_i/h = 55-i+(2i-55)/L. Arbitrarily large L gives the same old cell.
// Store both the limiting depths in bins and the exact strict test at an integer width.
const L=1000000;
const P=Array.from({length:n},(_,i)=>(55-i)*L+2*i-55);
const signed=P.concat(P.map(x=>-x));
const distance=signed.map((_,a)=>Math.min((a+1)%(2*n),(2*n-a-1)%(2*n)));
assert(signed.every((v,i)=>Math.abs(v-signed[(i+1)%(2*n)])<L) &&
  signed.filter(v=>v>55*L).length===1,"strict angular test and inactive gap terms");
const bins=P.map(x=>Math.floor(x/L+56));
assert(bins.every((v,i)=>v===111-i-Number(i<28)),"old free cell");
assert(signed.every((v,i)=>{
  const shift=(56-distance[i])*L-v;
  return 0<Math.abs(shift) && Math.abs(shift)<L;
}),"integer width limits");
const neighbor=loadProfile(input,bins).w;
let near=0n;
for (let i=0;i<n;++i) for (let j=i+1;j<n;++j) near+=2n*neighbor[i][j]*det(z[i],z[j]);
const nearLo=near*capDen*digits/(H*unit**2n*capNum);
assert(nearLo>999701130000n,"normalized evaluation at the anchor profile");

// All positive-coordinate central bins, with gradient directions exp(i*j*pi/112).
const central=loadProfile(input,Array(n).fill(56)).w;
const sins=Array.from({length:n},(_,j)=>cosPi(Math.abs(n/2-j),n));
let center=0n;
for (let i=0;i<n;++i) for (let j=i+1;j<n;++j) {
  const w=2n*central[i][j];
  center+=w*sins[j-i][w>=0n?0:1];
}
const centerLo=center*capDen*digits/(H*S*capNum);
assert(centerLo>999928500000n,"normalized central evaluation");

const areaUp=(a,b)=>ceil(a*piHi**2n*digits,b*piUnits);
const areaLo=(a,b)=>a*piLo**2n*digits/(b*piUnits);
const bisectedNum=737877064811692678202731938521n, bisectedDen=1194666547200000000000000000000n;
const reference=[["free",areaLo(BASE_NUM,BASE_DEN),areaUp(BASE_NUM,BASE_DEN)],
  ["bisected",areaLo(bisectedNum,bisectedDen),areaUp(bisectedNum,bisectedDen)]];
let least;
const results=[];
for (let m=1;m<=n;++m) {
  const limiting=distance.map(d=>d<m);
  const exact=signed.map(v=>v>(56-m)*L);
  for (const active of [limiting,exact]) for (let j=1;j<n;++j) {
    const mass=BigInt(m*m-Math.max(m-j,0)**2-Math.max(m-n+j,0)**2);
    const value=wedge[j].reduce((total,v,a)=>active[a]?total+v:total,0n);
    assert(value>0n && mass>0n,"positive transverse response");
    const cost=value*N*piUnits*micro/(unit**2n*2n*mass*piHi**2n);
    if (least===undefined || cost<least) least=cost;
  }
  if ([1,12,38,112].includes(m)) {
    const controls={};
    for (const [name,lo,up] of reference) {
      const fixed=up+ceil((digits-nearLo)*micro,least);
      controls[name]={fixed_scale_upper:out(fixed)};
      if (m<=38) {
        assert(lo*least>nearLo*micro, "endpoint of the possible scale interval");
        const rhs=ceil(digits*((centerLo-nearLo)*micro+up*least),least*centerLo);
        controls[name].arbitrary_nonnegative_scale_upper=out(rhs);
      }
    }
    results.push({max_width_in_bins:m,certified_cost_per_action_in_millionths:String(least),...controls});
  }
}
console.log(JSON.stringify({near_value_lower:out(nearLo),center_value_lower:out(centerLo),results},null,2));
