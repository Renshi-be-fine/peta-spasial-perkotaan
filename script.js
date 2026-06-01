// Polyfill untuk roundRect (jika belum ada)
if (!CanvasRenderingContext2D.prototype.roundRect) {
  CanvasRenderingContext2D.prototype.roundRect = function(x, y, w, h, r) {
    if (w < 2 * r) r = w / 2;
    if (h < 2 * r) r = h / 2;
    this.moveTo(x + r, y);
    this.lineTo(x + w - r, y);
    this.quadraticCurveTo(x + w, y, x + w, y + r);
    this.lineTo(x + w, y + h - r);
    this.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
    this.lineTo(x + r, y + h);
    this.quadraticCurveTo(x, y + h, x, y + h - r);
    this.lineTo(x, y + r);
    this.quadraticCurveTo(x, y, x + r, y);
    return this;
  };
}

// ============================================================
// KONSTANTA
// ============================================================
const MAP_W = 2800, MAP_H = 1900;
const MM_W = 160, MM_H = 110;

const C = {
  land:       '#f7f3e8',
  hwBorder:   '#4a4a4a',
  hwFill:     '#9e9e9e',
  mainBorder: '#5a5a5a',
  mainFill:   '#b0b0b0',
  sideBorder: '#6a6a6a',
  sideFill:   '#c0c0c0',
  routeBFS:   '#e65100', routeBFSGlow:  'rgba(230,81,0,0.4)',
  routeDijk:  '#1565c0', routeDijkGlow: 'rgba(21,101,192,0.4)',
  building:   '#d8d2c8', roof: '#a0522d'
};

// ============================================================
// STATE
// ============================================================
const S = {
  zoom:1, minZ:0.15, maxZ:5,
  px:0, py:0,
  drag:false, dsx:0, dsy:0, dpx:0, dpy:0,
  nodes:[], edges:[], adj:{}, cc:{},
  lakes:[],
  startN:0, endN:10,
  bfsPath:[], dijkPath:[],
  animSteps:true,
  trackActive:false, trackPaused:false,
  trackT:0, trackSpeed:0.0018,
  trackSpeedMult:1,
  raf:null,
  camFollow:true,
  trailBFS:[], trailDijk:[],
  wheelAngle:0,
  nodeBuildings:[],
  nodeTrees:[]
};

// ============================================================
// CANVAS
// ============================================================
const mc = document.getElementById('mc');
const ctx = mc.getContext('2d');
mc.width = MAP_W; mc.height = MAP_H;

// ============================================================
// HELPER — mkRnd (dibutuhkan generateMap)
// ============================================================
function mkRnd(seed){
  let r=(seed^0xdeadbeef)>>>0;
  return ()=>{
    r=Math.imul(r^(r>>>16),0x45d9f3b);
    r=Math.imul(r^(r>>>16),0x45d9f3b);
    r^=r>>>16; return (r>>>0)/0xffffffff;
  };
}

// ============================================================
// BFS
// ============================================================
function bfs(start,end,adj){
  const Q=[[start]],vis=new Set([start]);
  while(Q.length){
    const p=Q.shift(),n=p[p.length-1];
    if(n===end)return p;
    for(const nb of(adj[n]||[])){
      if(!vis.has(nb.to)){vis.add(nb.to);Q.push([...p,nb.to]);}
    }
  }
  return [];
}

// ============================================================
// DIJKSTRA
// ============================================================
function dijkstra(start,end,adj,nodes){
  const dist={},prev={};
  nodes.forEach(n=>dist[n.id]=Infinity);
  dist[start]=0;
  const pq=[{id:start,d:0}];
  while(pq.length){
    pq.sort((a,b)=>a.d-b.d);
    const {id,d}=pq.shift();
    if(id===end)break;
    if(d>dist[id])continue;
    for(const nb of(adj[id]||[])){
      const nd=d+nb.weight;
      if(nd<dist[nb.to]){dist[nb.to]=nd;prev[nb.to]=id;pq.push({id:nb.to,d:nd});}
    }
  }
  if(dist[end]===Infinity)return [];
  const p=[];let c=end;
  while(c!==undefined){p.unshift(c);c=prev[c];}
  return p;
}

function pathDist(path,adj){
  let t=0;
  for(let i=0;i<path.length-1;i++){
    const nb=adj[path[i]]?.find(n=>n.to===path[i+1]);
    if(nb)t+=nb.weight;
  }
  return t;
}

function pathKm(path,adj){
  let t=0;
  for(let i=0;i<path.length-1;i++){
    const nb=adj[path[i]]?.find(n=>n.to===path[i+1]);
    if(nb)t+=(nb.dist||nb.weight);
  }
  return (t/400).toFixed(2);
}

// ============================================================
// GENERATE MAP — Graph Construction
// ============================================================
function generateMap(seed){
  const rnd=mkRnd(seed||Math.floor(Math.random()*1e9));

  const labels=['Pelabuhan','Pasar Besar','Kampus UMRAH','Grand Mall','Terminal Bus','Perumahan',
    'Bandara','Stasiun KA','RSUD','Taman Kota','Polres','Masjid Raya',
    'Hotel Grand','SMA Negeri 1','Bank BRI','Balai Kota','Lapangan','Pantai Indah',
    'Kawasan Industri','Pusat Kuliner','SPBU 24H','Gedung Seni','Museum Kota','Taman Budaya'];
  const icons=['⚓','🛒','🎓','🏬','🚌','🏘','✈','🚉','🏥','🌳','🚓','🕌',
    '🏨','🏫','🏦','🏛','⛳','🏖','🏭','🍜','⛽','🎭','🏛','🎪'];
  const rtypes=[0,1,1,1,1,2, 0,1,1,2,2,2, 1,2,1,1,2,2, 0,2,2,2,1,2];

  const cols=6,rows=4;
  const padX=180,padY=160;
  const cW=(MAP_W-padX*2)/cols,cH=(MAP_H-padY*2)/rows;
  const nodes=[];
  for(let i=0;i<24;i++){
    const c=i%cols,r=Math.floor(i/cols);
    const pos=()=>{
      const v=rnd();
      if(v<0.18) return 0.02+rnd()*0.10;
      if(v<0.35) return 0.88+rnd()*0.10;
      return 0.18+rnd()*0.64;
    };
    nodes.push({
      id:i,
      x:Math.round(padX+cW*c+cW*pos()),
      y:Math.round(padY+cH*r+cH*pos()),
      label:labels[i],icon:icons[i],rtype:rtypes[i]
    });
  }

  // ------------------------------------------------------------------
  // GRAPH CONSTRUCTION: MST + extra density + guaranteed no dead-ends
  // ------------------------------------------------------------------
  const edges=[];
  function hasEdge(a,b){
    return edges.some(e=>(e.from===a&&e.to===b)||(e.from===b&&e.to===a));
  }
  function addEdge(a,b){
    if(a===b||hasEdge(a,b))return;
    const dx=nodes[a].x-nodes[b].x,dy=nodes[a].y-nodes[b].y;
    const d=Math.sqrt(dx*dx+dy*dy);
    edges.push({from:a,to:b,weight:Math.round(d),dist:Math.round(d)});
  }

  // 1) MST Prim – menjamin semua node terhubung
  const inMST=new Set([0]);
  while(inMST.size<nodes.length){
    let minD=Infinity,best=null;
    for(const u of inMST){
      for(let v=0;v<nodes.length;v++){
        if(inMST.has(v))continue;
        const dx=nodes[u].x-nodes[v].x,dy=nodes[u].y-nodes[v].y;
        const d=Math.sqrt(dx*dx+dy*dy);
        if(d<minD){minD=d;best={from:u,to:v};}
      }
    }
    inMST.add(best.to);
    addEdge(best.from,best.to);
  }

  // 2) Extra density edges
  for(let i=0;i<nodes.length;i++){
    for(let j=i+1;j<nodes.length;j++){
      if(hasEdge(i,j))continue;
      const dx=nodes[i].x-nodes[j].x,dy=nodes[i].y-nodes[j].y;
      const d=Math.sqrt(dx*dx+dy*dy);
      if(d<500&&rnd()<0.42)addEdge(i,j);
    }
  }

  // 3) Loop guarantee: setiap node punya degree >= 2
  let changed=true;
  while(changed){
    changed=false;
    const deg=new Array(nodes.length).fill(0);
    edges.forEach(e=>{deg[e.from]++;deg[e.to]++;});
    for(let i=0;i<nodes.length;i++){
      if(deg[i]>=2)continue;
      let nearest=-1,nearD=Infinity;
      for(let j=0;j<nodes.length;j++){
        if(j===i||hasEdge(i,j))continue;
        const dx=nodes[i].x-nodes[j].x,dy=nodes[i].y-nodes[j].y;
        const d=Math.sqrt(dx*dx+dy*dy);
        if(d<nearD){nearD=d;nearest=j;}
      }
      if(nearest>=0){addEdge(i,nearest);changed=true;}
    }
  }

  // 4) Bypass edges: koneksi jarak jauh
  const candidates=[];
  for(let i=0;i<nodes.length;i++){
    for(let j=i+1;j<nodes.length;j++){
      if(hasEdge(i,j))continue;
      const dx=nodes[i].x-nodes[j].x,dy=nodes[i].y-nodes[j].y;
      const d=Math.sqrt(dx*dx+dy*dy);
      if(d>600)candidates.push({i,j,d});
    }
  }
  candidates.sort((a,b)=>b.d-a.d);
  const bypassEdges=[];
  const usedNodes=new Set();
  for(const c of candidates){
    if(bypassEdges.length>=5)break;
    if(usedNodes.has(c.i)||usedNodes.has(c.j))continue;
    bypassEdges.push(c);
    usedNodes.add(c.i); usedNodes.add(c.j);
    addEdge(c.i,c.j);
    edges[edges.length-1].bypass=true;
  }

  const lakeSeeds=[
    {cx:MAP_W*0.22, cy:MAP_H*0.52, rx:105,ry:72, label:'Danau Sari'},
    {cx:MAP_W*0.73, cy:MAP_H*0.28, rx:82, ry:58, label:'Kolam Taman'},
    {cx:MAP_W*0.53, cy:MAP_H*0.74, rx:125,ry:88, label:'Danau Kota'},
  ];
  const lakes=lakeSeeds.filter(l=>{
    return nodes.every(n=>Math.hypot(n.x-l.cx,n.y-l.cy)>180);
  });

  // Cache curves — akan diisi oleh Cinto (fungsi getCP/getCPBypass/arcTable)
  const cc={};
  edges.forEach(e=>{
    const a=nodes[e.from],b=nodes[e.to];
    const {cp1,cp2}=e.bypass?getCPBypass(a,b):getCP(a,b);
    const T=arcTable(a,cp1,cp2,b);
    cc[`${e.from}-${e.to}`]={cp1,cp2,T,len:T[T.length-1].s,a,b,bypass:e.bypass};
    const Tr=arcTable(b,cp2,cp1,a);
    cc[`${e.to}-${e.from}`]={cp1:cp2,cp2:cp1,T:Tr,len:Tr[Tr.length-1].s,a:b,b:a,bypass:e.bypass};
  });

  const adj={};
  nodes.forEach(n=>adj[n.id]=[]);
  edges.forEach(e=>{
    adj[e.from].push({to:e.to,   weight:e.weight,dist:e.dist||e.weight,bypass:!!e.bypass});
    adj[e.to].push(  {to:e.from, weight:e.weight,dist:e.dist||e.weight,bypass:!!e.bypass});
  });

  // Buildings & Trees — akan diisi Cinto
  const nodeBuildings=[],nodeTrees=[];
  nodes.forEach(node=>{
    const edgeAngles=[];
    for(const nb of(adj[node.id]||[])){
      const o=nodes[nb.to];
      edgeAngles.push(Math.atan2(o.y-node.y,o.x-node.x)*180/Math.PI);
    }
    let bestAngle=0,maxMinDiff=-Infinity;
    for(let a=0;a<360;a+=30){
      let minDiff=180;
      for(const ea of edgeAngles){
        let diff=Math.abs(a-ea);
        diff=Math.min(diff,360-diff);
        if(diff<minDiff)minDiff=diff;
      }
      if(minDiff>maxMinDiff){maxMinDiff=minDiff;bestAngle=a;}
    }
    const rad=bestAngle*Math.PI/180;
    const dist=105;
    const bx=node.x+Math.cos(rad)*dist;
    const by=node.y+Math.sin(rad)*dist;
    let type='default',w=56,h=48;
    if(node.label.includes('SMA')){type='school';w=72;h=54;}
    else if(node.label.includes('Bandara')){type='airport';w=88;h=60;}
    else if(node.label.includes('Mall')||node.label.includes('Pasar')){type='mall';w=74;h=62;}
    else if(node.label.includes('RSUD')){type='hospital';w=68;h=58;}
    else if(node.label.includes('Masjid')){type='mosque';w=64;h=62;}
    else if(node.label.includes('Hotel')){type='hotel';w=60;h=56;}
    else if(node.label.includes('Bank')||node.label.includes('Balai')){type='office';w=64;h=52;}
    else if(node.label.includes('SPBU')){type='gasstation';w=58;h=46;}
    else if(node.label.includes('Kampus')){type='university';w=80;h=58;}
    else if(node.label.includes('Terminal')||node.label.includes('Stasiun')){type='station';w=72;h=52;}
    else if(node.label.includes('Museum')){type='museum';w=70;h=56;}
    nodeBuildings.push({nodeId:node.id,x:bx-w/2,y:by-h/2,width:w,height:h,type,label:node.label});
    const trad=bestAngle*Math.PI/180;
    const treeDist=140;
    nodeTrees.push({nodeId:node.id,
      x:node.x+Math.cos(trad)*treeDist,
      y:node.y+Math.sin(trad)*treeDist,
      size:17,type:['pine','round','palm'][node.id%3]});
  });

  return {nodes,edges,adj,cc,nodeBuildings,nodeTrees,lakes};
}

// ============================================================
// runAlgos — memanggil BFS & Dijkstra, tampilkan hasil
// ============================================================
const sleep=ms=>new Promise(r=>setTimeout(r,ms));

async function runAlgos(){
  const algo=document.querySelector('input[name="algo"]:checked')?.value||'both';
  S.startN=parseInt(document.getElementById('selS').value);
  S.endN=parseInt(document.getElementById('selE').value);
  if(S.startN===S.endN){notify('⚠️ Pilih node berbeda');return;}
  stopTrack();
  let bP=[],dP=[],bT=0,dT=0;
  if(algo==='both'||algo==='bfs'){const t=performance.now();bP=bfs(S.startN,S.endN,S.adj);bT=performance.now()-t;}
  if(algo==='both'||algo==='dijkstra'){const t=performance.now();dP=dijkstra(S.startN,S.endN,S.adj,S.nodes);dT=performance.now()-t;}
  const nm=id=>S.nodes[id]?.label||id;
  document.getElementById('rBP').textContent=bP.length?bP.map(nm).join(' → '):'(tidak ditemukan)';
  document.getElementById('rBD').textContent=bP.length?pathKm(bP,S.adj)+' km':'–';
  document.getElementById('rBH').textContent=bP.length?bP.length-1:'–';
  document.getElementById('rBT').textContent=bT.toFixed(3);
  document.getElementById('rDP').textContent=dP.length?dP.map(nm).join(' → '):'(tidak ditemukan)';
  document.getElementById('rDD').textContent=dP.length?pathKm(dP,S.adj)+' km':'–';
  document.getElementById('rDH').textContent=dP.length?dP.length-1:'–';
  document.getElementById('rDT').textContent=dT.toFixed(3);
  const sumBox=document.getElementById('rSummary');
  if(bP.length&&dP.length&&algo==='both'){
    const bKm=parseFloat(pathKm(bP,S.adj)),dKm=parseFloat(pathKm(dP,S.adj));
    const bH=bP.length-1,dH=dP.length-1;
    const samePath=JSON.stringify(bP)===JSON.stringify(dP);
    const kmWinner=dKm<=bKm?'Dijkstra':'BFS';
    const hopWinner=bH<=dH?'BFS':'Dijkstra';
    const kmDiff=Math.abs(bKm-dKm).toFixed(2);
    const hopDiff=Math.abs(bH-dH);
    let html=`<b style="color:#f59e0b">BFS</b>&nbsp;&nbsp;${bH} hop · ${bKm} km<br>
<b style="color:#10b981">Dijkstra</b>&nbsp;&nbsp;${dH} hop · ${dKm} km<br>
<span style="border-top:1px solid #2d3d5a;display:block;margin:5px 0"></span>`;
    if(samePath){
      html+=`<span style="color:#8a94b0">Jalur sama — coba titik lain atau klik Acak Posisi.</span>`;
    }else{
      html+=`<b style="color:#4a9eff">${kmWinner}</b> hemat <b>${kmDiff} km</b> &nbsp;·&nbsp; <b style="color:#4a9eff">${hopWinner}</b> hemat <b>${hopDiff} hop</b><br>
<span style="color:#6a7490;font-size:.65rem">BFS abaikan jarak → min singgah · Dijkstra hitung jarak → min km</span>`;
    }
    sumBox.innerHTML=html; sumBox.style.display='block';
  }else{
    sumBox.style.display='none';
  }
  if(S.animSteps){
    S.bfsPath=[];S.dijkPath=[];
    const mx=Math.max(bP.length,dP.length);
    for(let i=1;i<=mx;i++){
      S.bfsPath=bP.slice(0,i);S.dijkPath=dP.slice(0,i);
      draw(S.bfsPath,S.dijkPath,null,null);
      await sleep(180);
    }
    S.bfsPath=bP;S.dijkPath=dP;
  }else{
    S.bfsPath=bP;S.dijkPath=dP;
    draw(S.bfsPath,S.dijkPath,null,null);
  }
  notify('✅ Rute ditemukan!');
  await sleep(400);
  S.trackT=0;S.trailBFS=[];S.trailDijk=[];S.wheelAngle=0;
  startTrack(true);
}

// ============================================================
// UI — populateSel & notify & clearRes
// ============================================================
function populateSel(){
  const ss=document.getElementById('selS'),se=document.getElementById('selE');
  ss.innerHTML=se.innerHTML='';
  S.nodes.forEach(n=>{
    ss.appendChild(new Option(`${n.icon} ${n.label}`,n.id));
    se.appendChild(new Option(`${n.icon} ${n.label}`,n.id));
  });
  ss.value=0; se.value=Math.floor(S.nodes.length*0.55);
  S.startN=0; S.endN=Math.floor(S.nodes.length*0.55);
  document.getElementById('stN').textContent=S.nodes.length;
  document.getElementById('stE').textContent=S.edges.length;
}

function notify(msg){
  const box=document.getElementById('nbox');
  const el=document.createElement('div');
  el.className='notif'; el.textContent=msg;
  box.appendChild(el);
  requestAnimationFrame(()=>el.classList.add('show'));
  setTimeout(()=>{el.classList.remove('show');setTimeout(()=>el.remove(),220);},2600);
}

function clearRes(){
  ['rBP','rDP'].forEach(id=>document.getElementById(id).textContent='–');
  ['rBD','rBH','rBT','rDD','rDH','rDT'].forEach(id=>document.getElementById(id).textContent='–');
  const sb=document.getElementById('rSummary');
  if(sb)sb.style.display='none';
}

function init(seed){
  const res=generateMap(seed);
  Object.assign(S,{nodes:res.nodes,edges:res.edges,adj:res.adj,cc:res.cc,
    nodeBuildings:res.nodeBuildings,nodeTrees:res.nodeTrees,lakes:res.lakes,
    bfsPath:[],dijkPath:[]});
  stopTrack(); populateSel(); clearRes(); draw();
}

// ============================================================
// EVENT LISTENERS
// ============================================================
document.getElementById('btnZI').onclick=()=>zoomTo(S.zoom*1.3);
document.getElementById('btnZO').onclick=()=>zoomTo(S.zoom/1.3);
document.getElementById('btnZR').onclick=()=>{
  const vp=document.getElementById('vp');
  const fz=Math.min(vp.clientWidth/MAP_W,vp.clientHeight/MAP_H)*0.94;
  S.zoom=fz; S.px=(vp.clientWidth-MAP_W*fz)/2; S.py=(vp.clientHeight-MAP_H*fz)/2; applyXform();
};
const vpEl=document.getElementById('vp');
vpEl.addEventListener('wheel',e=>{
  e.preventDefault();
  const r=e.currentTarget.getBoundingClientRect();
  zoomTo(S.zoom*(e.deltaY<0?1.13:0.88),e.clientX-r.left,e.clientY-r.top);
},{passive:false});
vpEl.addEventListener('mousedown',e=>{
  S.drag=true; S.dsx=e.clientX; S.dsy=e.clientY; S.dpx=S.px; S.dpy=S.py;
  vpEl.classList.add('drag');
});
window.addEventListener('mousemove',e=>{
  if(!S.drag)return;
  S.px=S.dpx+(e.clientX-S.dsx); S.py=S.dpy+(e.clientY-S.dsy);
  clampPan(); applyXform();
});
window.addEventListener('mouseup',()=>{S.drag=false; vpEl.classList.remove('drag');});
document.getElementById('btnRand').onclick=()=>{stopTrack();init(Math.floor(Math.random()*1e9));notify('🔀 Peta baru!');};
document.getElementById('btnRandPos').onclick=()=>{
  const n=S.nodes.length;
  const indices=[...Array(n).keys()];
  indices.sort(()=>Math.random()-0.5);
  let found=false;
  for(let a=0;a<indices.length&&!found;a++){
    for(let b=0;b<indices.length&&!found;b++){
      const s=indices[a],e=indices[b];
      if(s===e)continue;
      const bPath=bfs(s,e,S.adj);
      const dPath=dijkstra(s,e,S.adj,S.nodes);
      if(bPath.length>0&&dPath.length>0&&JSON.stringify(bPath)!==JSON.stringify(dPath)){
        S.startN=s; S.endN=e;
        document.getElementById('selS').value=s;
        document.getElementById('selE').value=e;
        found=true;
        notify(`🎯 ${S.nodes[s].label} → ${S.nodes[e].label} (jalur beda!)`);
        runAlgos();
      }
    }
  }
  if(!found)notify('⚠️ Semua jalur sama di peta ini, coba Acak Map');
};
document.getElementById('btnTrack').onclick=()=>{
  if(!S.trackActive){S.trackT=0;S.trailBFS=[];S.trailDijk=[];startTrack();}
  else if(!S.trackPaused)pauseTrack();
  else resumeTrack();
};
document.getElementById('btnRun').onclick=runAlgos;
document.getElementById('btnReset').onclick=()=>{stopTrack();S.bfsPath=[];S.dijkPath=[];draw();clearRes();notify('↺ Reset');};
document.getElementById('tglAnim').onclick=function(){S.animSteps=!S.animSteps;this.classList.toggle('on',S.animSteps);};
document.getElementById('tglCam').onclick=function(){S.camFollow=!S.camFollow;this.classList.toggle('on',S.camFollow);notify(S.camFollow?'📷 Kamera follow ON':'📷 Kamera follow OFF');};
const speedLabels=['','Sangat Lambat','Lambat','Normal','Agak Cepat','Cepat','Sangat Cepat','Turbo','MAX'];
const speedMults=[0,0.3,0.6,1,1.8,3,5,8,14];
document.getElementById('speedSlider').oninput=function(){const v=parseInt(this.value);S.trackSpeedMult=speedMults[v]||1;document.getElementById('speedLbl').textContent=speedLabels[v]||'Normal';};
document.getElementById('selS').onchange=e=>{S.startN=parseInt(e.target.value);draw(S.bfsPath,S.dijkPath);};
document.getElementById('selE').onchange=e=>{S.endN=parseInt(e.target.value);draw(S.bfsPath,S.dijkPath);};
document.getElementById('btnAbout').onclick=()=>document.getElementById('mdbg').classList.add('open');
document.getElementById('btnMdClose').onclick=()=>document.getElementById('mdbg').classList.remove('open');
document.getElementById('mdbg').onclick=e=>{if(e.target===document.getElementById('mdbg'))document.getElementById('mdbg').classList.remove('open');};
mmc.addEventListener('click',e=>{
  const r=mmc.getBoundingClientRect();
  const mx=(e.clientX-r.left)/MM_W, my=(e.clientY-r.top)/MM_H;
  const vp=document.getElementById('vp');
  S.px=-(mx*MAP_W*S.zoom-vp.clientWidth/2);
  S.py=-(my*MAP_H*S.zoom-vp.clientHeight/2);
  clampPan(); applyXform();
});

window.addEventListener('load',()=>{
  const vp=document.getElementById('vp');
  const fz=Math.min(vp.clientWidth/MAP_W,vp.clientHeight/MAP_H)*0.92;
  S.zoom=fz; S.px=(vp.clientWidth-MAP_W*fz)/2; S.py=(vp.clientHeight-MAP_H*fz)/2;
  init(); applyXform();
  notify('🗺️ Peta siap! Jarak dalam km · BFS=min hop, Dijkstra=min km');
});
