"use strict";

// Exact verification of an interval-dependent diagonal rescaling of the transported form.
const {INPUT,npzReader,reconstruct,piInterval,assert}=require("./issue163_fourier_caps.cjs");
const D=32000000000000, T0=31970639125404, Z=100000000;
const K=[0,8,16,24,32,36,40,42,44,46,48,50,52,54,55,56];
const SIGMA=[100259911,100259899,100257343,100258354,100241253,100250506,100231480,100236670,100214191,100206599,100040345,99799793,99606872,100703694,100522025];
const ENDPOINT_FILE="agent_n112_uniform_patterns.npz";
const ENDPOINT_HASH="8df3c962bddb82441b0cc7f833058ba7e07c25d9989a1fab97a80540003e9da6";
function group(x){
  for(let j=1;j<K.length;j++)if(Math.abs(x)<K[j])return j-1;
  throw Error("scalar cell midpoint out of range");
}
function canonicalParent(b){
  const n=b.length;
  let min=n;for(const v of b)min=Math.min(min,v,n-1-v);
  function at(s,reverse,i){
    let k=(s+i)%n;if(reverse)k=n-1-k;
    return Math.floor((s+i)/n)%2?n-1-b[k]:b[k];
  }
  let start=0,rev=0;
  for(let r=0;r<2;r++)for(let s=0;s<2*n;s++){
    if(at(s,r,0)!==min)continue;
    for(let j=0;j<n;j++){const a=at(s,r,j),v=at(start,rev,j);if(a!==v){if(a<v){start=s;rev=r;}break;}}
  }
  const out=[],perm=[];
  for(let j=0;j<n;j++){out.push(at(start,rev,j));const i=(start+j)%n;perm.push(rev?n-1-i:i);}
  return [String.fromCharCode(...out),perm];
}
function endpointState(doc,st56,field,maps,endpoint,hash){
  const n=112,boxes=endpoint("boxes"), count=boxes.length/n;
  assert(count===116986,"endpoint count");
  const parentBoxes=doc.levels.find(l=>l.n===56).pattern_boxes;
  const missing=field("completed56_ids"),extra=field("completed56_diagonals"),completed=new Map(Array.from(missing,(p,j)=>[p,j]));
  const parentIndex=new Map(),pd=new Float64Array(parentBoxes.length*56);let kept=0;
  for(let p=0;p<parentBoxes.length;p++){
    const b=parentBoxes[p];parentIndex.set(String.fromCharCode(...b),p);
    if(completed.has(p)){const j=completed.get(p);pd.set(extra.subarray(j*56,j*56+56),p*56);}
    else{
      assert(b.every((v,j)=>v===st56.boxes[kept*56+j]),"parent order");
      pd.set(st56.diagonal.subarray(kept*56,kept*56+56),p*56);kept++;
    }
  }
  assert(kept===st56.count && missing.length===28,"completed parent coverage");
  function coefficients(n,master){
    const id=maps("class_variable_"+n),sn=maps("class_scale_num_"+n),sd=maps("class_scale_den_"+n);
    return Array.from(id,(v,i)=>v<0?0:8*master[v]*sn[i]/sd[i]);
  }
  const parent=coefficients(56,field("parent_filled_master_numerators"));
  const w=coefficients(n,field("master_numerators")),parentId=maps("parent_class_all_112");
  const reps=maps("reps_112"),objN=maps("objective_num_112"),objD=maps("objective_den_112");
  const tab=new Int32Array(n**3).fill(-1),key=(k,a,b)=>(k*n+a)*n+b;
  const delta=w.map((v,i)=>Math.abs(v-(parentId[i]<0?0:parent[parentId[i]]/2)));
  let area=0n,old=0n;
  for(let i=0;i<w.length;i++){
    const k=reps[3*i],a=reps[3*i+1],b=reps[3*i+2],u=group(a-55.5),v=group(b-55.5);
    const twice=2*objN[i]/objD[i];assert(Number.isSafeInteger(twice)&&Number.isSafeInteger(w[i])&&Number.isSafeInteger(delta[i]),"edge units");
    const term=BigInt(twice)*BigInt(w[i]);old+=term;area+=term*BigInt(SIGMA[u])*BigInt(SIGMA[v]);
    assert(delta[i]===0||Math.min(a,111-a,b,111-b)<2,"endpoint support");
    const stack=[[k,a,b]];
    while(stack.length){
      const [j,x,y]=stack.pop(),t=key(j,x,y);if(tab[t]===i)continue;
      assert(tab[t]===-1,"disjoint endpoint orbits");tab[t]=i;stack.push([j,y,x],[j,111-x,111-y],[112-j,y,111-x]);
    }
  }
  assert(old*3552293236156n===2182536605945n*BigInt(n*n)*BigInt(T0),"unscaled finite action");
  const edgeId=(p,i,j)=>tab[key(j-i,boxes[p*n+i],boxes[p*n+j])];
  const diagonal=new BigInt64Array(boxes.length),cache=new Map();
  for(let p=0;p<count;p++){
    const b=boxes.subarray(p*n,(p+1)*n),d=new Float64Array(n);
    for(let parity=0;parity<2;parity++){
      const vals=Uint8Array.from({length:56},(_,j)=>b[parity+2*j]>>1),s=String.fromCharCode(...vals);
      let row=cache.get(s);
      if(!row){
        const [code,perm]=canonicalParent(vals),id=parentIndex.get(code);
        assert(id!==undefined,"identified parent");row=new Float64Array(56);
        for(let j=0;j<56;j++)row[perm[j]]=pd[id*56+j];cache.set(s,row);
      }
      for(let j=0;j<56;j++)d[2*j+parity]=row[j];
    }
    for(let i=0;i<n;i++){
      if(Math.min(b[i],111-b[i])>=2)continue;
      for(let j=0;j<n;j++){
        if(j===i||(j<i&&Math.min(b[j],111-b[j])<2))continue;
        const id=edgeId(p,Math.min(i,j),Math.max(i,j));assert(id>=0,"endpoint label");
        d[i]+=2*delta[id];d[j]+=2*delta[id];
      }
    }
    for(let j=0;j<n;j++){assert(Number.isSafeInteger(d[j]),"child diagonal units");diagonal[n*p+j]=BigInt(d[j]);}
  }
  assert(hash(new Uint8Array(diagonal.buffer))===field("diagonal_sha256_112"),"full 112 diagonal hash (little-endian)");
  return {n,boxes,count,diagonal,grid:Array.from({length:113},(_,i)=>i-56),edge:(p,i,j)=>w[edgeId(p,i,j)],area};
}

function propose(edge,n,scale,sweeps) {
  // Block-coordinate ascent supplies candidate diagonal entries in the unscaled matrix.
  const rank=3, w=edge.map((z,j)=>z*scale[Math.floor(j/n)]*scale[j%n]/D);
  const x=new Float64Array(n*rank),y=new Float64Array(n*rank),diag=new Float64Array(n);
  let seed=123+n;
  function rand(){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;}
  for(let i=0;i<n;i++){
    let norm=0;for(let k=0;k<rank;k++){const j=rank*i+k;x[j]=2*rand()-1;y[j]=2*rand()-1;norm+=x[j]**2+y[j]**2;}
    for(let k=0;k<rank;k++){x[rank*i+k]/=Math.sqrt(norm);y[rank*i+k]/=Math.sqrt(norm);}
  }
  for(let it=0;it<sweeps;it++){
    let change=0;
    for(let i=0;i<n;i++){
      const a=new Float64Array(rank),b=new Float64Array(rank);
      for(let j=0;j<n;j++){
        const c=w[i*n+j];if(!c)continue;
        for(let k=0;k<rank;k++){a[k]+=c*y[rank*j+k];b[k]-=c*x[rank*j+k];}
      }
      let norm=0;for(let k=0;k<rank;k++)norm+=a[k]**2+b[k]**2;
      norm=Math.sqrt(norm);diag[i]=norm;if(!norm)continue;
      for(let k=0;k<rank;k++){const j=rank*i+k,r=a[k]/norm,s=b[k]/norm;
        change=Math.max(change,Math.abs(r-x[j]),Math.abs(s-y[j]));x[j]=r;y[j]=s;}
    }
    if(change<1e-10)break;
  }
  return Array.from(diag,(v,i)=>Math.ceil(v*D/scale[i]**2));
}
function cholesky(d,edge,n,shift) {
  const a=new Float64Array(n*n),b=new Float64Array(n*n);
  for(let i=0;i<n;i++)for(let j=0;j<=i;j++){
    let r=i===j?d[i]/D-shift:0,s=edge[i*n+j]/D;
    for(let k=0;k<j;k++){
      const ar=a[n*i+k],ai=b[n*i+k],br=a[n*j+k],bi=b[n*j+k];
      r-=ar*br+ai*bi;s-=ai*br-ar*bi;
    }
    if(i===j){if(!(r>0))return null;a[i*n+j]=Math.sqrt(r);}
    else{a[i*n+j]=r/a[j*n+j];b[i*n+j]=s/a[j*n+j];}
  }
  return [a,b];
}
function checkGram(d,edge,n,xy) {
  const X=1000000000000000, xx=BigInt(X)**2n, den=BigInt(D);
  const [a,b]=xy.map(row=>Array.from(row,v=>{
    const i=Math.round(v*X);assert(Number.isSafeInteger(i),"Gram witness magnitude");return BigInt(i);
  }));
  const surplus=Array(n).fill(0n);
  for(let i=0;i<n;i++)for(let j=0;j<=i;j++){
    let u=0n,v=0n;
    for(let k=0;k<=j;k++){
      const ar=a[i*n+k],ai=b[i*n+k],br=a[j*n+k],bi=b[j*n+k];
      u+=ar*br+ai*bi;v+=ai*br-ar*bi;
    }
    if(i===j)surplus[i]+=BigInt(d[i])*xx-den*u;
    else{
      let r=den*u,s=BigInt(edge[i*n+j])*xx-den*v;
      const e=(r<0n?-r:r)+(s<0n?-s:s);surplus[i]-=e;surplus[j]-=e;
    }
  }
  return surplus.every(x=>x>=0n);
}
function lowerCost(st,p,ids,weights,oldCost,target) {
  const n=st.n,edge=new Float64Array(n*n);
  for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
    const w=st.edge(p,i,j);assert(Number.isSafeInteger(w),"matrix coefficient");
    edge[i*n+j]=w;edge[j*n+i]=-w;
  }
  const s=Array.from(ids,i=>SIGMA[i]/Z);
  let best=oldCost;
  for(const sweeps of [n<=28?130:240,n===112?1400:650,3000]){
    const trial=propose(edge,n,s,sweeps);
    const weighted=trial.reduce((v,a,i)=>v+2n*BigInt(a)*weights[ids[i]],0n);
    if(weighted>=best && best<=target)break;
    if(weighted>=best)continue;
    const shift=1e-11;
    let hi=320,xy=null,lo=0;
    for(;hi<1e11;hi*=4){
      xy=cholesky(trial.map(v=>v+hi),edge,n,shift);
      if(xy)break;lo=hi;
    }
    if(!xy)continue;
    for(let k=0;k<12 && hi-lo>1;k++){const mid=Math.floor((lo+hi)/2),res=cholesky(trial.map(v=>v+mid),edge,n,shift);
      if(res){hi=mid;xy=res;}else lo=mid;}
    const d=trial.map(v=>v+hi);
    const cost=d.reduce((v,a,i)=>v+2n*BigInt(a)*weights[ids[i]],0n);
    if(cost<best && checkGram(d,edge,n,xy)){best=cost;if(best<=target)break;}
  }
  return best;
}
function verifyField(states,area){
  const denS=BigInt(Z)**2n,weights=SIGMA.map(s=>BigInt(s)**2n);
  const target=2n*BigInt(T0)*denS,report=[];
  let global=0n;
  for(const st of states){
    const n=st.n;
    const bucket=st.grid.slice(0,-1).map((v,i)=>group((v+st.grid[i+1])/2));
    const valid=st.grid.slice(0,-1).map((v,i)=>!K.some(k=>(v<k&&k<st.grid[i+1])||(v< -k&&-k<st.grid[i+1])));
    let largest=0n,repairs=0,attempts=0,worst=-1;
    for(let p=0;p<st.count;p++){
      const sums=new Float64Array(SIGMA.length),ids=new Uint8Array(n);
      for(let i=0;i<n;i++){
        const z=st.boxes[n*p+i],b=bucket[z];assert(valid[z],"constant scalar weight in reached leaf");
        ids[i]=b;sums[b]+=Number(st.diagonal[n*p+i]);
      }
      let cost=0n;for(let j=0;j<sums.length;j++){assert(Number.isSafeInteger(sums[j]),"group trace");cost+=BigInt(sums[j])*weights[j];}
      if(n<112)cost*=2n;
      if(cost>target){attempts++;const replacement=lowerCost(st,p,ids,weights,cost,target);if(replacement<cost)repairs++;cost=replacement;}
      if(cost>largest){largest=cost;worst=p;}
    }
    if(largest>global)global=largest;
    report.push({anchors:n,profiles:st.count,attempts,accepted:repairs,worst,trace_numerator:String(largest)});
  }
  const numerator=2n*area,denominator=112n**2n*global,unit=10n**18n;
  const factor=numerator*unit/denominator,pi=piInterval()[0];
  return {slopes:SIGMA,scale_denominator:Z,levels:report,objective_twice_scaled:String(area),
    global_trace_numerator:String(global),trace_denominator:String(2n*BigInt(D)*denS),
    pi_squared_factor_floor_1e18:String(factor),area_floor_1e18:String(factor*pi*pi/(10n**96n))};
}
function replayReweight(raw,io) {
  for(const [key,[file,digest]] of Object.entries(INPUT))assert(io.hash(raw[key])===digest,"source hash "+file);
  assert(io.hash(raw.endpoints)===ENDPOINT_HASH,"112 endpoint source hash");
  const doc=JSON.parse(io.utf8(io.ungzip(raw.source)));
  const [old,field,maps,endpoint]=["old","field","maps","endpoints"].map(key=>npzReader(raw[key],io.inflate));
  const states=[14,28,56].map(n=>reconstruct(doc.levels.find(row=>row.n===n),old,field,maps,io.hash));
  const child=endpointState(doc,states[2],field,maps,endpoint,io.hash);states.push(child);
  return verifyField(states,child.area);
}
if(typeof module!=="undefined" && require.main===module){
  const fs=require("node:fs"),path=require("node:path"),zlib=require("node:zlib"),crypto=require("node:crypto");
  const dir=process.argv[2];if(!dir)throw Error("Pass the finite certificate directory.");
  const raw={endpoints:fs.readFileSync(path.join(dir,ENDPOINT_FILE))};
  for(const [key,[file]] of Object.entries(INPUT))raw[key]=fs.readFileSync(path.join(dir,file));
  const io={hash:data=>crypto.createHash("sha256").update(data).digest("hex"),utf8:data=>data.toString("utf8"),
    ungzip:zlib.gunzipSync,inflate:zlib.inflateRawSync};
  console.log(JSON.stringify(replayReweight(raw,io),null,2));
}
