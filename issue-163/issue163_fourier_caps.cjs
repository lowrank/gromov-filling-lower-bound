"use strict";

// The public entry point is at the end. All acceptance comparisons use integers.
const N = 112, QD = 32000000000000, T = 31970639125404;
const SLOPE_DEN = 1000, RATE_DEN = 1000000000, BINS = 5000;
const KNOTS = [0,8,16,24,32,36,40,42,44,46,48,50,52,54,56];
const Q = [1000,988,997,1036,1043,1213,1200,1222,1144,1000,700,650,500,1000];
const SCALE = 10n ** 48n, TRIG = 10n ** 16n, ANGLE = 100000000;
const SOLVE = 1000000000000;
const abs = x => x < 0n ? -x : x;
function assert(ok, message) { if (!ok) throw Error(message); }
function floorDiv(a,b) { return a / b - (a % b < 0n ? 1n : 0n); }
function ceilDiv(a,b) { return -floorDiv(-a,b); }
function asInt(x) { assert(Number.isSafeInteger(x), "integer range"); return BigInt(x); }

function atanInterval(m) {
  let lo=0n, hi=0n, power=m;
  for (let k=0n;k<100n;k++) {
    const den=(2n*k+1n)*power;
    if(k%2n===0n){lo+=SCALE/den;hi+=ceilDiv(SCALE,den);}
    else{lo-=ceilDiv(SCALE,den);hi-=SCALE/den;}
    power*=m*m;
  }
  return [lo, hi+ceilDiv(SCALE,201n*power)];
}
function piInterval() {
  const a=atanInterval(5n), b=atanInterval(239n);
  return [16n*a[0]-4n*b[1],16n*a[1]-4n*b[0]];
}
// Taylor's formula with alternating tail for cos on the first quadrant.
function cosineTable(pi) {
  const angles=[];
  for(let j=0;j<=112;j++){
    const x0=pi[0]*BigInt(j)/224n, x1=ceilDiv(pi[1]*BigInt(j),224n);
    let a=SCALE,b=SCALE,lo=a,hi=b;
    for(let k=1n;k<=23n;k++){
      const den=SCALE*SCALE*(2n*k-1n)*(2n*k);
      a=a*x0*x0/den; b=ceilDiv(b*x1*x1,den);
      if(k%2n){lo-=b;hi-=a;}else{lo+=a;hi+=b;}
    }
    hi+=ceilDiv(b*x1*x1,SCALE*SCALE*47n*48n);
    angles.push([lo,hi]);
  }
  return j=>{
    j=((j%448)+448)%448;
    if(j>224)j=448-j;
    if(j<=112)return angles[j];
    const [lo,hi]=angles[224-j];return [-hi,-lo];
  };
}
function roundedCos(cos,j,den) {
  const [lo,hi]=cos(j);
  const k=floorDiv((lo+hi)*den+SCALE,2n*SCALE);
  assert((k-1n)*SCALE<=lo*den && hi*den<=(k+1n)*SCALE,"trig enclosure");
  return k;
}
function makeShape(q){
  assert(q.length===KNOTS.length-1 && q.every(v=>Number.isSafeInteger(v)&&v>=0&&v<=4000),"slope grid");
  const v=[0];
  for(let k=0,j=0;k<56;k++){while(k>=KNOTS[j+1])j++;v.push(v[k]+q[j]);}
  return k=>k<0?-v[-k]:v[k];
}
function lowerProjection(sum,err,den){return floorDiv(2n*asInt(sum-err)*BigInt(BINS),den);}
function capBin(c, val, cosines, den){
  let sum=0,err=0;
  for(let j=0;j<N;j++){
    const i=Math.min(j,N-j), x=val(Math.max(c-i,i-56));
    sum+=x*cosines[i]; err+=Math.abs(x);
  }
  return Number(lowerProjection(sum,err,den));
}
function leafEnvelope(st,p,val){
  const n=st.n, m=N/n, L=[],H=[];
  for(let i=0;i<2*n;i++){
    const box=st.boxes[p*n+i%n], neg=i>=n;
    L[i]=neg?-st.grid[box+1]:st.grid[box];
    H[i]=neg?-st.grid[box]:st.grid[box+1];
  }
  for(let s=0;s<2;s++){
    for(let j=1;j<=2*n;j++){const i=j%(2*n), a=(j-1)%(2*n);L[i]=Math.max(L[i],L[a]-m);H[i]=Math.min(H[i],H[a]+m);}
    for(let i=2*n-1;i>=0;i--){const a=(i+1)%(2*n);L[i]=Math.max(L[i],L[a]-m);H[i]=Math.min(H[i],H[a]+m);}
  }
  const lo=[],hi=[];
  for(let k=0;k<N;k++){
    const j=Math.floor(k/m),u=k%m;
    lo[k]=val(Math.max(-56,L[j]-u,L[j+1]-m+u));
    hi[k]=val(Math.min(56,H[j]+u,H[j+1]+m-u));
    assert(lo[k]<=hi[k],"empty angular enclosure");
  }
  return [lo,hi];
}
function shellRange(st,p,val,cs,den) {
  const [lo,hi]=leafEnvelope(st,p,val);
  let min=0,max=0,err=0;
  for(let k=0;k<N;k++)err+=Math.max(Math.abs(lo[k]),Math.abs(hi[k]));
  // Every normal of the polygon is tested. The index shift by N changes sign.
  for(let d=0;d<N;d++){
    let a=0,b=0;
    for(let k=0;k<N;k++){
      const c=cs[k-d+N];
      a+=c*(c>=0?lo[k]:hi[k]); b+=c*(c>=0?hi[k]:lo[k]);
    }
    min=Math.max(min,a,-b);max=Math.max(max,b,-a);
  }
  return [Number(lowerProjection(min,err,den)),Number(ceilDiv(2n*asInt(max+err)*BigInt(BINS),den))];
}

function linearSolve(diag,off,rhsR,rhsI) {
  const n=diag.length, A=new Float64Array(n*n),B=new Float64Array(n*n);
  for(let i=0;i<n;i++)for(let j=0;j<=i;j++){
    let r=i===j?diag[i]:0,s=off[i*n+j];
    for(let k=0;k<j;k++){
      const ar=A[i*n+k],ai=B[i*n+k],br=A[j*n+k],bi=B[j*n+k];
      r-=ar*br+ai*bi;s-=ai*br-ar*bi;
    }
    if(i===j){if(!(r>0))return null;A[i*n+j]=Math.sqrt(r);}
    else{A[i*n+j]=r/A[j*n+j];B[i*n+j]=s/A[j*n+j];}
  }
  const x=rhsR.slice(),y=rhsI.slice();
  for(let i=0;i<n;i++){
    for(let j=0;j<i;j++){const r=A[i*n+j],s=B[i*n+j];x[i]-=r*x[j]-s*y[j];y[i]-=s*x[j]+r*y[j];}
    x[i]/=A[i*n+i];y[i]/=A[i*n+i];
  }
  for(let i=n-1;i>=0;i--){
    for(let j=i+1;j<n;j++){const r=A[j*n+i],s=B[j*n+i];x[i]-=r*x[j]+s*y[j];y[i]-=r*y[j]-s*x[j];}
    x[i]/=A[i*n+i];y[i]/=A[i*n+i];
  }
  return [x,y];
}
// A numerical inverse proposes a vector. A rational residual decides the rate.
function certifiedRate(st,p,slope,C,S,local=null) {
  const n=st.n, t=local?local.slack:asInt(T-st.trace[p]), smax=Math.max(...slope);
  if(t===0n||smax===0)return 0;
  const qd=local?local.denominator:BigInt(QD), multiplier=BigInt(n);
  const H=Array.from({length:n},(_,i)=>multiplier*(local?local.diagonal[i]:asInt(st.diagonal[n*p+i]))+t);
  const W=Array(n*n).fill(0n);
  for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
    const a=local?local.edge(i,j):asInt(st.edge(p,i,j));
    W[i*n+j]=multiplier*a;W[j*n+i]=-multiplier*a;
  }
  const rh=slope.map((v,i)=>v*Number(C[i])/(n*SLOPE_DEN*Number(TRIG)));
  const ih=slope.map((v,i)=>v*Number(S[i])/(n*SLOPE_DEN*Number(TRIG)));
  const scale=Number(multiplier*qd);
  const xy=linearSolve(H.map(x=>Number(x)/scale),W.map(x=>Number(x)/scale),rh,ih);
  if(!xy)return 0;
  let resolution=SOLVE;
  if(local){
    const largest=Math.max(...xy[0].map(Math.abs),...xy[1].map(Math.abs));
    while(resolution>1 && largest*resolution>Number.MAX_SAFE_INTEGER/2)resolution/=10;
  }
  const proposed=xy.map(row=>row.map(v=>Math.round(resolution*v)));
  if(!proposed.every(row=>row.every(Number.isSafeInteger)))return 0;
  const [x,y]=proposed.map(row=>row.map(BigInt));
  const DC=BigInt(SLOPE_DEN)*TRIG, mult=qd*BigInt(resolution);
  let e=0n,dot=0n,energy=0n,realLower=0n;
  for(let i=0;i<n;i++){
    let r=H[i]*x[i],s=H[i]*y[i];
    for(let j=0;j<n;j++)if(W[i*n+j]!==0n){const w=W[i*n+j];r-=w*y[j];s+=w*x[j];}
    const v=BigInt(slope[i]);
    const er=abs(v*C[i]*mult-r*DC),ei=abs(v*S[i]*mult-s*DC);
    if(er>e)e=er;if(ei>e)e=ei;
    const center=C[i]*x[i]+S[i]*y[i],error=abs(x[i])+abs(y[i]);
    dot+=v*(center+error);
    if(local){energy+=x[i]*r+y[i]*s;realLower+=v*(center-error);}
  }
  if(local && realLower>0n){
    assert(energy>=0n,"nonnegative quadratic form");
    const up=ceilDiv(BigInt(local.rateDen)*BigInt(n)*DC**2n*energy,qd*realLower**2n);
    if(up<BigInt(local.upper))local.upper=Number(up);
  }
  e+=BigInt(smax)*mult;
  const num=dot*BigInt(SLOPE_DEN)*t+2n*BigInt(n*smax)*e;
  const den=BigInt(n*SLOPE_DEN)*DC*BigInt(resolution)*t;
  assert(num>0n,"inverse-vector bound");
  return Number(BigInt(local?local.rateDen:RATE_DEN)*den/num);
}
function verify(states,q=Q,field=null) {
  const pi=piInterval(),cos=cosineTable(pi), val=makeShape(q);
  const cs=Array.from({length:2*N+1},(_,i)=>Number(roundedCos(cos,2*(i-N),BigInt(ANGLE))));
  const den=BigInt(N*N*SLOPE_DEN)*BigInt(ANGLE);
  const first=n=>capBin(n,val,cs.slice(N),den);
  const top=first(54), boundary=first(56);
  const cosHalf=cos(1)[0];
  assert(top>0 && BigInt(top)*SCALE*SCALE<BigInt(boundary)*cosHalf*cosHalf,"boundary winding");
  const rateDen=field?1000000000000:RATE_DEN;
  const rates=new Float64Array(top).fill(rateDen/40);
  const upperRates=field?new Float64Array(top).fill(rateDen/40):null;
  const records=[];
  for(const st of states){
    const n=st.n,minimum=n===14?0:first(n===28?48:52);
    const slopes=st.grid.slice(0,-1).map((a,i)=>{
      const b=st.grid[i+1],v=(val(b)-val(a))/(b-a);
      assert(Number.isSafeInteger(v) && !KNOTS.some(k=>(a<k&&k<b)||(a< -k&&-k<b)),"leaf slope cell");return v;
    });
    const C=[],S=[];
    for(let i=0;i<n;i++){C[i]=roundedCos(cos,224*i/n,TRIG);S[i]=roundedCos(cos,112-224*i/n,TRIG);}
    const cheap=new Float64Array(st.count),maxRate=rateDen/40;
    for(let p=0;p<st.count;p++){
      let sum=0;for(let i=0;i<n;i++)sum+=slopes[st.boxes[n*p+i]];
      const slack=field?field.budget-field.trace(st,p):asInt(T-st.trace[p]);assert(slack>=0n,"input trace exceeds budget");
      const num=BigInt(rateDen)*slack*BigInt(n*SLOPE_DEN)**2n;
      const d=(field?field.denominator:BigInt(QD))*BigInt(sum)**2n;
      cheap[p]=!d||num>=BigInt(maxRate)*d?maxRate:Number(num/d);
    }
    const order=Array.from({length:st.count},(_,i)=>i).sort((a,b)=>cheap[a]-cheap[b]);
    let ranges=0,inverse=0;
    for(const p of order){
      if(cheap[p]>=maxRate)break;
      const [l,h]=shellRange(st,p,val,cs,den);ranges++;
      const a=Math.max(0,minimum,l),b=Math.min(rates.length,h);
      if(a>=b)continue;
      let needed=0;for(let j=a;j<b;j++)needed=Math.max(needed,rates[j]);
      if(cheap[p]>=needed)continue;
      const s=Array.from(st.boxes.subarray(n*p,n*p+n),v=>slopes[v]);
      const local=field?{...field.matrix(st,p),rateDen,upper:maxRate}:null;
      const allowed=Math.max(cheap[p],certifiedRate(st,p,s,C,S,local));inverse++;
      for(let j=a;j<b;j++){
        rates[j]=Math.min(rates[j],allowed);
        if(local)upperRates[j]=Math.min(upperRates[j],Math.max(cheap[p]+1,local.upper));
      }
    }
    records.push({anchors:n,profiles:st.count,range_checks:ranges,inverse_attempts:inverse});
  }
  // Integrate exactly over polygonal shells. tan(pi/224) is bounded from below.
  const sinHalf=cos(111)[0],cosHi=cos(1)[1];
  let sum=0n;for(let j=0;j<rates.length;j++)sum+=BigInt(2*j+1)*BigInt(rates[j]);
  const ad=field?10n**18n:3552293236156n,an=field?field.factor:2182536605945n;
  const bd=(field?field.budget:BigInt(T))*BigInt(rateDen)*BigInt(BINS)**2n*cosHi;
  const bn=BigInt(2*N)*(field?field.denominator:BigInt(QD))*sinHalf*sum;
  const unit=10n**18n;
  const factor=(an*bd+bn*ad)*unit/(ad*bd);
  const area=factor*pi[0]*pi[0]/(SCALE*SCALE);
  const report={slope_numerators:q,slope_denominator:SLOPE_DEN,bin_denominator:BINS,shells:top,records,
    rate_denominator:rateDen,weighted_rate_numerator:String(sum),pi_squared_factor_floor_1e18:String(factor),
    area_floor_1e18:String(area)};
  if(field){
    let upperSum=0n;for(let j=0;j<upperRates.length;j++){
      assert(rates[j]<=upperRates[j],"two-sided shell comparison");
      upperSum+=BigInt(2*j+1)*BigInt(upperRates[j]);
    }
    const du=field.budget*BigInt(rateDen)*BigInt(BINS)**2n*cos(1)[0];
    const nu=BigInt(2*N)*field.denominator*cos(111)[1]*upperSum;
    const up=ceilDiv(10n**12n*pi[1]**2n*((an+1n)*du+nu*ad),SCALE**2n*du*ad);
    report.fixed_shell_rule_upper_1e12=String(up);
  }
  return report;
}

const INPUT = {
  source:["agent_best_60744_exact.json.gz","2dab89354e887ee076c71e1a825d568f5102c96758148f4cc1a4ab30fd960535"],
  old:["large_n_112_compact_certificate.npz","ea364d177e9b563e3260eacb2231275fbc99c435dd02ff629e6b9b043c366375"],
  field:["improve112_6081_transport_exact_compact_certificate.npz","985ab24c6caec546520750ffded97b583064cf81109635d2e4a905546a5767db"],
  maps:["large_n_14_28_56_112_maps.npz","ee35d911bbad2e2d669e4a6e3b38839b7a18aa8078d171861bc8766f3bc5bbde"]
};
function npzReader(raw,inflate) {
  const dv=new DataView(raw.buffer,raw.byteOffset,raw.byteLength);
  const u2=i=>dv.getUint16(i,true),u4=i=>dv.getUint32(i,true);
  let end=raw.length-22;while(end>=0 && u4(end)!==0x06054b50)end--;
  assert(end>=0,"ZIP end record");
  const files=new Map();let c=u4(end+16);
  const ascii=bytes=>String.fromCharCode(...bytes);
  for(let i=0;i<u2(end+10);i++){
    assert(u4(c)===0x02014b50,"ZIP directory");
    const key=ascii(raw.subarray(c+46,c+46+u2(c+28))).replace(/\.npy$/,"");
    const p=u4(c+42);assert(u4(p)===0x04034b50 && u2(p+8)===8,"ZIP compression");
    const begin=p+30+u2(p+26)+u2(p+28);files.set(key,[begin,begin+u4(c+20)]);
    c+=46+u2(c+28)+u2(c+30)+u2(c+32);
  }
  const cache=new Map();
  return key=>{
    if(cache.has(key))return cache.get(key);
    assert(files.has(key),"missing array "+key);
    const [a,b]=files.get(key),bytes=inflate(raw.subarray(a,b));
    assert(bytes[0]===147 && bytes[6]===1,"NPY format");
    const start=10+bytes[8]+256*bytes[9],header=ascii(bytes.subarray(10,start));
    const dtype=header.match(/'descr': '([^']+)'/)[1],v=new DataView(bytes.buffer,bytes.byteOffset+start,bytes.length-start);
    assert(header.includes("'fortran_order': False"),"NPY order");
    let result;
    if(dtype.startsWith("<U")){
      result="";for(let k=0;k<v.byteLength;k+=4){const s=v.getUint32(k,true);if(s)result+=String.fromCodePoint(s);}
    }else{
      assert(["<i8","<i4","|u1"].includes(dtype),"NPY integer format "+dtype);
      const width=dtype==="<i8"?8:dtype==="<i4"?4:1;result=width===1?new Uint8Array(v.byteLength):new Float64Array(v.byteLength/width);
      for(let j=0;j<result.length;j++){result[j]=width===1?v.getUint8(j):width===4?v.getInt32(j*4,true):Number(v.getBigInt64(j*8,true));assert(Number.isSafeInteger(result[j]),"NPY integer magnitude");}
    }
    cache.set(key,result);return result;
  };
}
function reconstruct(row,old,field,maps,hash) {
  const n=row.n, m=N/n;
  const grid=row.grid.map(s=>{const [a,b="1"]=String(s).split("/");const x=m*Number(a)/Number(b);assert(Number.isInteger(x),"grid alignment");return x;});
  const B=grid.length-1, key=(k,a,b)=>(k*B+a)*B+b;
  const table=new Int32Array(n*B*B).fill(-1);
  for(let id=0;id<row.representatives.length;id++){
    const queue=[row.representatives[id]];
    while(queue.length){
      const [k,a,b]=queue.pop(),j=key(k,a,b);
      if(table[j]===id)continue;
      assert(table[j]===-1,"disjoint coefficient orbits");table[j]=id;
      queue.push([k,b,a],[k,B-1-a,B-1-b],[n-k,b,B-1-a]);
    }
  }
  const variable=maps("class_variable_"+n),sn=maps("class_scale_num_"+n),sd=maps("class_scale_den_"+n);
  const coeff=master=>Array.from(variable,(v,i)=>v<0?0:8*master[v]*sn[i]/sd[i]);
  const source=coeff(old("baseline_master_numerators")),older=coeff(old("master_numerators")),now=coeff(field("master_numerators"));
  assert([source,older,now].every(x=>x.every(Number.isSafeInteger)),"coefficient units");
  const exceptions=[old,field].map(get=>{
    const ids=get("exception_ids_"+n),d=get("exception_diagonals_"+n);
    return new Map(Array.from(ids,(p,j)=>[p,d.subarray(j*n,(j+1)*n)]));
  });
  const kept=[];
  for(let i=0;i<row.pattern_boxes.length;i++){
    if(n!==56||row.pattern_boxes[i].every(a=>grid[a]>=-54&&grid[a+1]<=54))kept.push(i);
  }
  const count=kept.length,boxes=new Uint8Array(n*count),diagonal=new Float64Array(n*count),trace=new Float64Array(count);
  const intervalId=(p,i,j)=>table[key(j-i,boxes[n*p+i],boxes[n*p+j])];
  const scale=QD/Number(row.diagonal_denominator);assert(Number.isInteger(scale),"source diagonal units");
  for(let p=0;p<count;p++){
    const src=kept[p],s=n*p;
    boxes.set(row.pattern_boxes[src],s);
    if(exceptions[1].has(p))diagonal.set(exceptions[1].get(p),s);
    else{
      const ex=exceptions[0].get(p);
      for(let i=0;i<n;i++) diagonal[s+i]=ex?ex[i]:scale*row.diagonal_numerators[src][i];
      for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
        const k=intervalId(p,i,j);assert(k>=0,"pair cell");
        const change=Math.abs(now[k]-older[k])+(ex?0:Math.abs(older[k]-source[k]));
        diagonal[s+i]+=change;diagonal[s+j]+=change;
      }
    }
    for(let i=0;i<n;i++){assert(Number.isSafeInteger(diagonal[s+i])&&diagonal[s+i]>=0,"source diagonal");trace[p]+=diagonal[s+i];}
    assert(Number.isSafeInteger(trace[p])&&trace[p]<=T,"source trace");
  }
  const packed=new Uint8Array(diagonal.length*8),view=new DataView(packed.buffer);
  for(let i=0;i<diagonal.length;i++)view.setBigInt64(8*i,BigInt(diagonal[i]),true);
  assert(hash(packed)===field("diagonal_sha256_"+n),"transported diagonal hash at "+n);
  return {n,count,grid,boxes,diagonal,trace,edge:(p,i,j)=>now[intervalId(p,i,j)]};
}
function replay(raw,io) {
  for(const [key,[file,digest]] of Object.entries(INPUT))assert(io.hash(raw[key])===digest,"source hash "+file);
  const doc=JSON.parse(io.utf8(io.ungzip(raw.source)));
  const [old,field,maps]=["old","field","maps"].map(key=>npzReader(raw[key],io.inflate));
  assert(field("base_area_pi_squared_factor")==="2182536605945/3552293236156","finite action");
  const states=[14,28,56].map(n=>reconstruct(doc.levels.find(row=>row.n===n),old,field,maps,io.hash));
  assert(states.map(s=>s.count).join(",")==="53100,29410,14562","leaf coverage");
  return verify(states);
}
if(typeof module!=="undefined") module.exports={INPUT,npzReader,reconstruct,piInterval,assert,verify};
if(typeof module!=="undefined" && require.main===module){
  const fs=require("node:fs"),path=require("node:path"),zlib=require("node:zlib"),crypto=require("node:crypto");
  const dir=process.argv[2];
  if(!dir)throw Error("Pass the bundle's research/output/improve112_6081_certificate directory.");
  const raw={};for(const [key,[file]] of Object.entries(INPUT))raw[key]=fs.readFileSync(path.join(dir,file));
  const io={hash:data=>crypto.createHash("sha256").update(data).digest("hex"),utf8:data=>data.toString("utf8"),
    ungzip:zlib.gunzipSync,inflate:zlib.inflateRawSync};
  console.log(JSON.stringify(replay(raw,io),null,2));
}
