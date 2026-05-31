// ============================================================
// script.js — Peta Spasial Perkotaan
// INF11114 Grafika Komputer · UMRAH 2026
// ============================================================

// Konstanta dan state akan ditambahkan oleh Aldi Saputra
// Algoritma BFS & Dijkstra akan ditambahkan oleh Ardiansyah Riski
// Fungsi grafika komputer akan ditambahkan oleh Cinto Aprilman
// Animasi dan tracking akan ditambahkan oleh Ikhbal Maulana
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
// UI — populateSel, notify, clearRes
// ============================================================
function populateSel(){
  const ss=document.getElementById('selS'), se=document.getElementById('selE');
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
