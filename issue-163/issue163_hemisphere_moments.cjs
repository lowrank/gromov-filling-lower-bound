"use strict";

// A small floating-point quadrature on the round hemisphere. No norm or area
// certificate depends on the quadrature. Retain the range of the three old
// diagonal proposals whenever the finite certificate supplies no fixed replacement.
const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const zlib = require("node:zlib");
const {INPUT,assert} = require("./issue163_fourier_caps.cjs");
const {loadField, ENDPOINT_FILE, SIGMA, group} = require("./issue163_reweighted_field.cjs");
const dir = process.argv[2] || path.join(__dirname,"issue163_inputs");
const read = f=>fs.readFileSync(path.join(dir,f));
const raw={endpoints:read(ENDPOINT_FILE)};
for (const [key,[file]] of Object.entries(INPUT)) raw[key]=read(file);
const {states}=loadField(raw,{hash:x=>crypto.createHash("sha256").update(x).digest("hex"),
  utf8:b=>b.toString("utf8"),ungzip:zlib.gunzipSync,inflate:zlib.inflateRawSync});
const cap=0.9999999, n=112, h=Math.PI/n;
const corner=require("./issue163_midpoint_witness.json").bisection;
const bytes=zlib.gunzipSync(fs.readFileSync(path.join(__dirname,"issue163_free_diagonals.bin.gz")));
let pos=0;
const levels=new Map();
for (const st of states) {
  const rows=new Map(), replaced=new Map(), m=st.n;
  for (let j=0; j<st.count; ++j) rows.set(Buffer.from(st.boxes.subarray(j*m,(j+1)*m)).toString("latin1"),j);
  const count=bytes.readUInt32LE(pos), start=pos+4*(1+count);
  for (let j=0; j<count; ++j) replaced.set(bytes.readUInt32LE(pos+4*(1+j)),start+4*m*j);
  pos=start+4*m*count;
  const scales=st.grid.slice(0,-1).map((v,i)=>SIGMA[group((v+st.grid[i+1])/2)]/1e8);
  levels.set(m,{...st,rows,replaced,scales});
}
assert(pos===bytes.length,"diagonal block sizes");
function canonical(b,bins) {
  const m=b.length, first=Math.min(...b,...b.map(v=>bins-1-v));
  let key,perm;
  for (const reverse of [false,true]) for (let s=0; s<2*m; ++s) {
    const values=[],order=[];
    for (let j=0; j<m; ++j) {
      const i=(s+j)%m, index=reverse?m-1-i:i;
      const value=Math.floor((s+j)/m)%2 ? bins-1-b[index] : b[index];
      if (j===0 && value!==first) break;
      values.push(value); order.push(index);
    }
    if (values.length===m) {
      const candidate=String.fromCharCode(...values);
      if (key===undefined || candidate<key) {key=candidate;perm=order;}
    }
  }
  return {key,perm};
}
function proposals(level,row,b) {
  const m=level.n, offset=level.replaced.get(row);
  const scale=b.map(i=>level.scales[i]**2);
  if (offset!==undefined) return [scale.map((s,i)=>s*bytes.readUInt32LE(offset+4*i)/1e9/cap)];
  const den=m===112?64e12:32e12;
  const original=scale.map((s,i)=>Number(level.diagonal[row*m+i])*s/den);
  const total=original.reduce((s,v)=>s+v,0), room=cap-2e-9-total;
  return [.25,.85,0].map(share=>original.map((v,i)=>{
    const d=Math.floor((v+room*((1-share)/m+share*v/total))*64e12/scale[i]);
    return d*scale[i]/(64e12*cap);
  }));
}
// Each row contains trace and the two components of the doubled-angle moment.
function bounds(values) {
  return values[0].map((_,j)=>[Math.min(...values.map(v=>v[j])),Math.max(...values.map(v=>v[j]))]);
}
function moment(d,z) {
  return d.reduce(([m,x,y],v,i)=>[m+v,x+v*z[i][0],y+v*z[i][1]],[0,0,0]);
}
function inherited(P,z) {
  const m=P.length, level=levels.get(m), g=level.grid;
  const b=P.map(v=>g.findIndex(t=>t>v)-1);
  assert(b.every(i=>i>=0 && i<g.length-1),"open scalar bin");
  const {key,perm}=canonical(b,g.length-1), row=level.rows.get(key);
  if (row!==undefined) {
    const rotated=perm.map(i=>z[i]);
    return bounds(proposals(level,row,perm.map(i=>b[i])).map(d=>moment(d,rotated)));
  }
  assert(m>14 && Math.max(...P.map(Math.abs))<56-224/m,"uncovered terminal profile");
  const parity=(v,k)=>v.filter((_,j)=>j%2===k);
  const a=inherited(parity(P,0),parity(z,0)), b1=inherited(parity(P,1),parity(z,1));
  return a.map((range,j)=>range.map((v,i)=>(v+b1[j][i])/2));
}
function sample(height,offset) {
  const P=[],z=[];
  for (let i=0; i<n; ++i) {
    const angle=(i+1-offset)*h, a=Math.sin(angle), b=-height*Math.cos(angle);
    P.push(Math.asin(Math.sqrt(1-height**2)*Math.cos(angle))/h);
    z.push([(a*a-b*b)/(a*a+b*b),2*a*b/(a*a+b*b)]);
  }
  let block;
  if (Math.min(P[0],-P[n-1])>55) {
    let x=P[0]-55.5,y=P[n-1]+55.5;
    const reverse=x+y>0;
    if (reverse) [x,y]=[-y,-x];
    const name=y>=0 ? "parent" : (x+y<-.5 ? "left" : "right");
    const d=corner[name+"_diagonal"].map(v=>v/(1e14*cap));
    block=bounds([moment(reverse?d.reverse():d,z)]);
  } else block=inherited(P,z);
  const [trace,x,y]=block;
  const near=([a,b])=>Math.max(0,a,-b), far=([a,b])=>Math.max(Math.abs(a),Math.abs(b));
  const momentSq=[near(x)**2+near(y)**2,far(x)**2+far(y)**2];
  return [trace,[momentSq[0]/trace[1],momentSq[1]/trace[0]]];
}
function quadrature(radial,angular) {
  const mass=[0,0], variance=[0,0];
  for (let i=0; i<radial; ++i) for (let j=0; j<angular; ++j) {
    const t=(i+.5)/radial, [tr,v]=sample(t*t,(j+.5)/(2*angular));
    for (let k=0;k<2;++k) {mass[k]+=2*t*tr[k]; variance[k]+=2*t*v[k];}
  }
  return {radial,angular,rms_range:[Math.sqrt(variance[0]/mass[1]),Math.sqrt(variance[1]/mass[0])]};
}
for (const [r,a] of [[12,4],[24,6],[48,8],[96,8]]) console.log(JSON.stringify(quadrature(r,a)));
