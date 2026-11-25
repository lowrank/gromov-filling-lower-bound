"use strict";

// Rational unit-ball tests for scalar reweightings of the fixed finite form.
const {INPUT,piInterval,assert}=require("./issue163_fourier_caps.cjs");
const {loadField,ENDPOINT_FILE,ENDPOINT_STEPS,group}=require("./issue163_reweighted_field.cjs");
const NB=15,N=112n,Z=100000000n;
const abs=x=>x<0n?-x:x;
const zeros=()=>Array(NB*NB).fill(0n);

function actionMatrix(field,maps){
  const rep=maps("reps_112"),ids=maps("class_variable_112");
  const sn=maps("class_scale_num_112"),sd=maps("class_scale_den_112");
  const on=maps("objective_num_112"),od=maps("objective_den_112");
  const master=field("master_numerators"),steps=new Map(ENDPOINT_STEPS),A=zeros();
  for(let o=0;o<ids.length;o++){
    const den=BigInt(sd[o]),num=ids[o]<0?0n:8n*BigInt(master[ids[o]])*BigInt(sn[o]);
    assert(den>0n && num%den===0n,"finite coefficient units");
    const wt=2n*BigInt(on[o]),wd=BigInt(od[o]);
    assert(wd>0n && wt%wd===0n,"twice polygon weight");
    const t=(wt/wd)*(num/den+BigInt(steps.get(o)||0));
    const i=group(rep[3*o+1]-55.5),j=group(rep[3*o+2]-55.5);
    A[i*NB+j]+=t;A[j*NB+i]+=t;
  }
  return A; // denominator 2 * 112^2 * (32 * 10^12)
}

function phaseMatrix(st,w,V){
  const {n,p,rank,real,imag}=w;
  assert(st && n===st.n && Number.isInteger(p) && p>=0 && p<st.count,"terminal profile");
  assert((rank===1||rank===3) && real.length===rank*n && imag.length===rank*n,"witness shape");
  assert(real.every(Number.isSafeInteger) && imag.every(Number.isSafeInteger),"rational phase numerators");
  const a=real.map(BigInt),b=imag.map(BigInt),bins=[],M=zeros();
  for(let i=0;i<n;i++){
    const cell=st.boxes[n*p+i];
    bins.push(group((st.grid[cell]+st.grid[cell+1])/2));
    let norm=0n;
    for(let k=0;k<rank;k++){const j=rank*i+k;norm+=a[j]*a[j]+b[j]*b[j];}
    assert(norm<=V*V,"unit ball");
  }
  for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
    let phase=0n;
    for(let k=0;k<rank;k++){
      const u=rank*i+k,v=rank*j+k;phase+=a[u]*b[v]-b[u]*a[v];
    }
    const w=st.edge(p,i,j);assert(Number.isSafeInteger(w),"edge");
    const t=BigInt(w)*phase,u=bins[i],v=bins[j];
    M[u*NB+v]+=t;M[v*NB+u]+=t;
  }
  return M; // denominator (32 * 10^12) * V^2
}

function verifyCeilings(raw,io,data){
  const {states,field,maps}=loadField(raw,io);
  const center=data.center.map(BigInt),V=BigInt(data.phase_denominator),W=BigInt(data.weight_denominator);
  assert(center.length===NB && V>0n && W>0n,"normalizations");
  const A=actionMatrix(field,maps);
  const act=A.reduce((a,v,k)=>a+v*center[Math.floor(k/NB)]*center[k%NB],0n);
  assert(act===2n*2474701746017983670807146346984704n,"action at the reference multipliers");
  const matrices=data.witnesses.map(w=>phaseMatrix(states.find(st=>st.n===w.n),w,V));
  const report=[],upperPi=piInterval()[1];
  for(const [family,mixture] of Object.entries(data.mixtures)){
    assert(family==="planar"||family==="sdp","family");
    const M=zeros();let total=0n;
    for(const [id,num] of mixture){
      assert(Number.isSafeInteger(num) && num>=0 && matrices[id],"dual weight");
      assert(family!=="planar" || data.witnesses[id].rank===1,"planar rank");
      const w=BigInt(num);total+=w;
      for(let i=0;i<M.length;i++)M[i]+=w*matrices[id][i];
    }
    const F=1000000n;
    const tests=family==="sdp"?[[2000000n,1000128n],[5000000n,1000850n]]:
                                [[2000000n,1000131n],[5000000n,1000868n]];
    for(const [R,f] of tests){
      const H=A.map((v,k)=>2n*N*N*f*M[k]-F*W*V*V*v);
      const h=center.map((_,i)=>center.reduce((a,v,j)=>a+v*H[NB*i+j],0n));
      const surplus=h.reduce((a,v,i)=>a+v*center[i]-2n*R*abs(v),0n)-R*R*H.reduce((a,v)=>a+abs(v),0n);
      assert(surplus>0n,"strict polynomial inequality on the whole box");
      const num=10n**12n*upperPi*upperPi*f*total,den=10n**96n*F*W;
      const upper=(num+den-1n)/den;
      assert(upper<6100000000000n,"area ceiling below 6.1");
      report.push({family,radius_units_1e8:String(R),area_upper_units_1e12:String(upper)});
    }
  }
  assert(report.length===4,"four local ceilings");return report;
}

if(typeof module!=="undefined" && require.main===module){
  const fs=require("node:fs"),path=require("node:path"),zlib=require("node:zlib"),crypto=require("node:crypto");
  const dir=process.argv[2];if(!dir)throw Error("Pass the finite certificate directory.");
  const raw={endpoints:fs.readFileSync(path.join(dir,ENDPOINT_FILE))};
  for(const [key,[file]] of Object.entries(INPUT))raw[key]=fs.readFileSync(path.join(dir,file));
  const io={hash:data=>crypto.createHash("sha256").update(data).digest("hex"),utf8:data=>data.toString("utf8"),
    ungzip:zlib.gunzipSync,inflate:zlib.inflateRawSync};
  const data=JSON.parse(fs.readFileSync(path.join(__dirname,"issue163_reweight_phases.json"),"utf8"));
  console.log(JSON.stringify(verifyCeilings(raw,io,data),null,2));
}
