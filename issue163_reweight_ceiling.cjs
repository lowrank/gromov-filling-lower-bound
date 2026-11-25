"use strict";

// Rational unit-ball tests for scalar reweightings of the fixed finite form.
const {INPUT,piInterval,assert}=require("./issue163_fourier_caps.cjs");
const {loadField,ENDPOINT_FILE,group}=require("./issue163_reweighted_field.cjs");
const NB=15,N=112n;
const REFERENCE_STEPS=[[1,6714930082],[115,49203043],[280,10427640066]];
const abs=x=>x<0n?-x:x;
const zeros=()=>Array(NB*NB).fill(0n);

function actionMatrix(field,maps){
  const rep=maps("reps_112"),ids=maps("class_variable_112");
  const sn=maps("class_scale_num_112"),sd=maps("class_scale_den_112");
  const on=maps("objective_num_112"),od=maps("objective_den_112");
  const master=field("master_numerators"),steps=new Map(REFERENCE_STEPS),A=zeros();
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

// Four exact equations enforce equality of the constant and all three free coefficients.
function determinant(matrix){
  if(matrix.length===1)return matrix[0][0];
  return matrix[0].reduce((sum,v,j)=>{
    const minor=matrix.slice(1).map(row=>row.filter((_,k)=>k!==j));
    return sum+(j%2?-v:v)*determinant(minor);
  },0n);
}
function endpointCeiling(states,maps,A,data){
  const S=data.multipliers.map(BigInt),V=BigInt(data.phase_denominator),ids=REFERENCE_STEPS.map(r=>r[0]);
  assert(S.length===NB && V>0n,"free endpoint normalization");
  const rep=maps("reps_112"),on=maps("objective_num_112"),od=maps("objective_den_112");
  const target=[A.reduce((a,v,k)=>a+v*S[Math.floor(k/NB)]*S[k%NB],0n)*V*V/2n];
  for(const id of ids){
    const twice=2n*BigInt(on[id])/BigInt(od[id]);
    target.push(twice*S[group(rep[3*id+1]-55.5)]*S[group(rep[3*id+2]-55.5)]*V*V);
  }
  const report={};
  for(const [type,witnesses] of Object.entries(data.families)){
    assert((type==="planar"||type==="sdp") && witnesses.length===4,"four dual columns");
    const columns=witnesses.map(w=>{
      assert(type!=="planar"||w.rank===1,"planar endpoint rank");
      const st=states.find(x=>x.n===w.n),M=phaseMatrix(st,w,V);
      const c=[N*N*M.reduce((a,v,k)=>a+v*S[Math.floor(k/NB)]*S[k%NB],0n),0n,0n,0n];
      if(st.n===112){
        const n=st.n,r=w.rank,a=w.real.map(BigInt),b=w.imag.map(BigInt);
        const bin=Array.from(st.boxes.subarray(n*w.p,n*(w.p+1)),v=>group(v-55.5));
        for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
          const k=ids.indexOf(st.edgeId(w.p,i,j));if(k<0)continue;
          let g=0n;for(let l=0;l<r;l++)g+=a[i*r+l]*b[j*r+l]-b[i*r+l]*a[j*r+l];
          c[1+k]+=2n*N*N*g*S[bin[i]]*S[bin[j]];
        }
      }
      return c;
    });
    const L=target.map((_,i)=>columns.map(col=>col[i]));
    let den=determinant(L);
    assert(den!==0n,"independent endpoint tests");
    const weight=columns.map((_,j)=>determinant(L.map((row,i)=>row.map((v,k)=>k===j?target[i]:v))));
    if(den<0n){den=-den;for(let j=0;j<weight.length;j++)weight[j]=-weight[j];}
    assert(weight.every(w=>w>=0n),"nonnegative exact mixture");
    for(let k=0;k<4;k++){
      assert(columns.reduce((a,col,j)=>a+col[k]*weight[j],0n)===target[k]*den,"coefficient identity");
    }
    const pi=piInterval()[1],d=den*10n**96n;
    const upper=(10n**12n*pi*pi*weight.reduce((a,b)=>a+b,0n)+d-1n)/d;
    report[type]={area_upper_units_1e12:String(upper),profiles:witnesses.map(w=>[w.n,w.p])};
  }
  assert(report.sdp && BigInt(report.sdp.area_upper_units_1e12)<6090500000000n,"endpoint PSD ceiling");
  return report;
}

// Endpoint slopes have the same two scalar factors on every occurrence of an orbit.
function jointCeiling(states,maps,A,center,data){
  const V=BigInt(data.phase_denominator),E=BigInt(data.weight_denominator),ids=REFERENCE_STEPS.map(r=>r[0]);
  const on=maps("objective_num_112"),od=maps("objective_den_112");
  const target=ids.map(id=>(2n*BigInt(on[id])/BigInt(od[id]))*V*V);
  const matrices=[],columns=[];
  for(const w of data.witnesses){
    assert(w.rank===1,"planar joint cut");
    const st=states.find(s=>s.n===w.n),M=phaseMatrix(st,w,V),col=[0n,0n,0n];
    if(st.n===112){
      const a=w.real.map(BigInt),b=w.imag.map(BigInt);
      for(let i=0;i<112;i++)for(let j=i+1;j<112;j++){
        const k=ids.indexOf(st.edgeId(w.p,i,j));if(k>=0)col[k]+=2n*N*N*(a[i]*b[j]-b[i]*a[j]);
      }
    }
    matrices.push(M);columns.push(col);
  }
  const solve=data.solve_indices,coarse=data.coarse_index,fixed=data.weights.map(BigInt);
  assert(E>0n && solve.length===3 && new Set(solve).size===3 && fixed.length===columns.length,"mixture data");
  assert(data.witnesses[coarse].n<112 && columns[coarse].every(v=>v===0n),"interior slack witness");
  const L=target.map((_,i)=>solve.map(j=>columns[j][i]));
  const rhs=target.map((v,k)=>columns.reduce((y,col,j)=>solve.includes(j)?y:y-col[k]*fixed[j],v*E));
  const det=determinant(L);assert(det!==0n,"independent free coefficients");
  const m=abs(det),den=E*m,w=fixed.map(v=>v*m);
  for(let j=0;j<3;j++){
    const d=determinant(L.map((row,i)=>row.map((v,k)=>k===j?rhs[i]:v)));
    w[solve[j]]=det>0n?d:-d;
  }
  assert(w.every(v=>v>=0n),"joint nonnegative weights");
  for(let k=0;k<3;k++){
    assert(columns.reduce((u,col,j)=>u+col[k]*w[j],0n)===target[k]*den,"global endpoint cancellation");
  }
  const H=A.map((v,k)=>2n*N*N*matrices.reduce((a,M,j)=>a+w[j]*M[k],0n)-den*V*V*v);
  const Q=matrices[coarse].map(v=>2n*N*N*m*v),total=w.reduce((a,v)=>a+v,0n);
  const pi=piInterval()[1],report=[];
  for(const R of [2000000n,5000000n]){
    function positive(e){
      const h=H.map((v,k)=>v+e*Q[k]),t=center.map((_,i)=>center.reduce((a,v,j)=>a+v*h[NB*i+j],0n));
      return t.reduce((a,v,i)=>a+v*center[i]-2n*R*abs(v),0n)>R*R*h.reduce((a,v)=>a+abs(v),0n);
    }
    let lo=-1n,hi=2000000000n;assert(positive(hi),"box dominance");
    while(hi-lo>1n){const mid=(lo+hi)/2n;if(positive(mid))hi=mid;else lo=mid;}
    assert(positive(hi),"joint polynomial inequality");
    const u=10n**12n*pi*pi*(total+hi*m),v=den*10n**96n,upper=(u+v-1n)/v;
    assert(upper<6100000000000n,"joint ceiling below 6.1");
    report.push({radius_units_1e8:String(R),area_upper_units_1e12:String(upper)});
  }
  return report;
}

function verifyCeilings(raw,io,data,cuts){
  const {states,field,maps}=loadField(raw,io,REFERENCE_STEPS);
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
  assert(report.length===4,"four local ceilings");
  return {multiplier_boxes:report,free_endpoints:endpointCeiling(states,maps,A,cuts),joint_planar:jointCeiling(states,maps,A,cuts.multipliers.map(BigInt),cuts.joint)};
}

if(typeof module!=="undefined" && require.main===module){
  const fs=require("node:fs"),path=require("node:path"),zlib=require("node:zlib"),crypto=require("node:crypto");
  const dir=process.argv[2];if(!dir)throw Error("Pass the finite certificate directory.");
  const raw={endpoints:fs.readFileSync(path.join(dir,ENDPOINT_FILE))};
  for(const [key,[file]] of Object.entries(INPUT))raw[key]=fs.readFileSync(path.join(dir,file));
  const io={hash:data=>crypto.createHash("sha256").update(data).digest("hex"),utf8:data=>data.toString("utf8"),
    ungzip:zlib.gunzipSync,inflate:zlib.inflateRawSync};
  const data=JSON.parse(fs.readFileSync(path.join(__dirname,"issue163_reweight_phases.json"),"utf8"));
  const cuts=JSON.parse(fs.readFileSync(path.join(__dirname,"issue163_endpoint_cuts.json"),"utf8"));
  console.log(JSON.stringify(verifyCeilings(raw,io,data,cuts),null,2));
}
