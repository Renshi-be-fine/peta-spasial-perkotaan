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
// KONSTANTA (DIMODIFIKASI: WARNA KONTRAST, JALAN LEBAR ABU-ABU)
// ============================================================
const MAP_W = 2800, MAP_H = 1900;
const MM_W = 160, MM_H = 110;

const C = {
  land:       '#f7f3e8',            // lebih terang biar kontras dengan jalan abu
  hwBorder:   '#4a4a4a',            // abu gelap untuk border jalan utama
  hwFill:     '#9e9e9e',            // abu terang untuk fill jalan utama
  mainBorder: '#5a5a5a',            // abu sedang untuk jalan sedang
  mainFill:   '#b0b0b0',            // abu muda
  sideBorder: '#6a6a6a',            // abu kehitaman untuk jalan kecil
  sideFill:   '#c0c0c0',            // abu terang
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
// BÉZIER & ARC-LENGTH
// ============================================================
function bez3(t,p0,p1,p2,p3){
  const u=1-t;
  return {x:u*u*u*p0.x+3*u*u*t*p1.x+3*u*t*t*p2.x+t*t*t*p3.x,
          y:u*u*u*p0.y+3*u*u*t*p1.y+3*u*t*t*p2.y+t*t*t*p3.y};
}
function arcTable(p0,p1,p2,p3,n=160){
  const T=[{t:0,s:0}]; let cum=0,prev=p0;
  for(let i=1;i<=n;i++){
    const t=i/n,pt=bez3(t,p0,p1,p2,p3);
    const dx=pt.x-prev.x,dy=pt.y-prev.y;
    cum+=Math.sqrt(dx*dx+dy*dy);
    T.push({t,s:cum}); prev=pt;
  }
  return T;
}
function arcLookup(T,s){
  const tot=T[T.length-1].s,tgt=Math.max(0,Math.min(s,tot));
  let lo=0,hi=T.length-1;
  while(lo<hi-1){const m=(lo+hi)>>1;if(T[m].s<tgt)lo=m;else hi=m;}
  const seg=T[hi].s-T[lo].s;
  if(seg<1e-9)return T[lo].t;
  return T[lo].t+(tgt-T[lo].s)/seg*(T[hi].t-T[lo].t);
}
function mkRnd(seed){
  let r=(seed^0xdeadbeef)>>>0;
  return ()=>{
    r=Math.imul(r^(r>>>16),0x45d9f3b);
    r=Math.imul(r^(r>>>16),0x45d9f3b);
    r^=r>>>16; return (r>>>0)/0xffffffff;
  };
}
function getCP(a,b){
  const seed=Math.min(a.id,b.id)*6271+Math.max(a.id,b.id)*7919;
  const rnd=mkRnd(seed);
  const dx=b.x-a.x,dy=b.y-a.y,d=Math.sqrt(dx*dx+dy*dy);
  const perp=Math.atan2(dy,dx)+Math.PI/2;
  const maxOff=d*0.09;
  const amp1=(rnd()-0.5)*2*maxOff,amp2=(rnd()-0.5)*2*maxOff;
  return {
    cp1:{x:a.x+dx*0.33+Math.cos(perp)*amp1,y:a.y+dy*0.33+Math.sin(perp)*amp1},
    cp2:{x:a.x+dx*0.67+Math.cos(perp)*amp2,y:a.y+dy*0.67+Math.sin(perp)*amp2}
  };
}
// Kurva bypass: melengkung keluar jauh dari pusat peta supaya tidak menimpa jalan lain
function getCPBypass(a,b){
  const dx=b.x-a.x,dy=b.y-a.y,d=Math.sqrt(dx*dx+dy*dy);
  const perp=Math.atan2(dy,dx)+Math.PI/2;
  // Arahkan lengkungan menjauhi pusat peta
  const cx=MAP_W/2,cy=MAP_H/2;
  const midX=a.x+dx*0.5,midY=a.y+dy*0.5;
  // Kalau titik tengah edge sudah di luar pusat, lengkungkan lebih ke luar lagi
  const toEdge=Math.atan2(midY-cy,midX-cx);
  const outward=Math.cos(toEdge)*Math.cos(perp)+Math.sin(toEdge)*Math.sin(perp)>0?1:-1;
  const off=d*0.42*outward; // offset 42% dari panjang edge → kurva sangat lebar
  return {
    cp1:{x:a.x+dx*0.25+Math.cos(perp)*off*0.8, y:a.y+dy*0.25+Math.sin(perp)*off*0.8},
    cp2:{x:a.x+dx*0.75+Math.cos(perp)*off*0.8, y:a.y+dy*0.75+Math.sin(perp)*off*0.8}
  };
}
function edgeType(e){
  const a=S.nodes[e.from],b=S.nodes[e.to];
  if(!a||!b)return 2;
  return Math.min(a.rtype,b.rtype);
}
// ============================================================
// JALAN DIBUAT LEBAR DAN WARNA ABU-ABU
// ============================================================
function roadW(e){
  const t=edgeType(e);
  if(t===0) return [28, 34];   // jalan utama lebar 28px
  if(t===1) return [20, 26];   // jalan sedang lebar 20px
  return [12, 18];             // jalan kecil lebar 12px
}

// ============================================================
// GENERATE MAP
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
    // ~35% node ditaruh sangat dekat tepi sel → edge dengan tetangga jadi pendek (~0.2km)
    // ~65% node di tengah sel → edge ke tetangga jadi panjang (~1.2–2km)
    // Ini menjamin selalu ada situasi: "1 hop jauh" vs "2–3 hop pendek-pendek"
    // sehingga BFS dan Dijkstra konsisten pilih jalur berbeda
    const pos=()=>{
      const v=rnd();
      if(v<0.18) return 0.02+rnd()*0.10;  // sangat dekat tepi kiri/atas
      if(v<0.35) return 0.88+rnd()*0.10;  // sangat dekat tepi kanan/bawah
      return 0.18+rnd()*0.64;             // tengah sel, tersebar lebar
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
    // weight = jarak pixel asli (400 unit ≈ 1 km)
    // Dijkstra: minimum total jarak · BFS: minimum hop
    edges.push({from:a,to:b,weight:Math.round(d),dist:Math.round(d)});
  }

  // 1) MST Prim – guarantees full connectivity
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

  // 2) Extra density edges (short random connections)
  for(let i=0;i<nodes.length;i++){
    for(let j=i+1;j<nodes.length;j++){
      if(hasEdge(i,j))continue;
      const dx=nodes[i].x-nodes[j].x,dy=nodes[i].y-nodes[j].y;
      const d=Math.sqrt(dx*dx+dy*dy);
      if(d<500&&rnd()<0.42)addEdge(i,j);
    }
  }

  // 3) LOOP GUARANTEE: ensure every node has degree ≥ 2
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



  // ------------------------------------------------------------------
  // BYPASS EDGES: 4–5 koneksi jarak jauh, kurva melengkung keluar
  // Tidak menimpa jalan existing karena offset bezier-nya besar (40–55% dari jarak)
  // Menciptakan trade-off BFS vs Dijkstra: 1 hop jauh vs beberapa hop pendek
  // ------------------------------------------------------------------
  // Kumpulkan semua pasangan yang belum terhubung, urutkan dari yang terjauh
  const candidates=[];
  for(let i=0;i<nodes.length;i++){
    for(let j=i+1;j<nodes.length;j++){
      if(hasEdge(i,j)) continue;
      const dx=nodes[i].x-nodes[j].x, dy=nodes[i].y-nodes[j].y;
      const d=Math.sqrt(dx*dx+dy*dy);
      if(d>600) candidates.push({i,j,d}); // hanya yang jaraknya >600px (~1.5km)
    }
  }
  candidates.sort((a,b)=>b.d-a.d);
  // Ambil 5 pasang terjauh yang posisinya tersebar (tidak semua dari pojok yang sama)
  const bypassEdges=[];
  const usedNodes=new Set();
  for(const c of candidates){
    if(bypassEdges.length>=5) break;
    // Batasi agar satu node tidak punya lebih dari 1 bypass edge (supaya tidak menumpuk)
    if(usedNodes.has(c.i)||usedNodes.has(c.j)) continue;
    bypassEdges.push(c);
    usedNodes.add(c.i); usedNodes.add(c.j);
    addEdge(c.i,c.j);
    // Tandai edge ini sebagai bypass supaya bisa digambar berbeda
    edges[edges.length-1].bypass=true;
  }

  // ------------------------------------------------------------------
  const lakeSeeds=[
    {cx:MAP_W*0.22, cy:MAP_H*0.52, rx:105,ry:72, label:'Danau Sari'},
    {cx:MAP_W*0.73, cy:MAP_H*0.28, rx:82, ry:58, label:'Kolam Taman'},
    {cx:MAP_W*0.53, cy:MAP_H*0.74, rx:125,ry:88, label:'Danau Kota'},
  ];
  const lakes=lakeSeeds.filter(l=>{
    return nodes.every(n=>Math.hypot(n.x-l.cx,n.y-l.cy)>180);
  });

  // ------------------------------------------------------------------
  // CACHE CURVES
  // ------------------------------------------------------------------
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
    adj[e.from].push({to:e.to,   weight:e.weight, dist:e.dist||e.weight, bypass:!!e.bypass});
    adj[e.to].push(  {to:e.from, weight:e.weight, dist:e.dist||e.weight, bypass:!!e.bypass});
  });

  // ------------------------------------------------------------------
  // BUILDINGS & TREES (offset away from roads)
  // ------------------------------------------------------------------
  const nodeBuildings=[],nodeTrees=[];
  nodes.forEach(node=>{
    const edgeAngles=[];
    for(const nb of(adj[node.id]||[])){
      const o=nodes[nb.to];
      edgeAngles.push(Math.atan2(o.y-node.y,o.x-node.x)*180/Math.PI);
    }
    // find direction with most gap from any edge
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

    const trad=bestAngle*Math.PI/180;  // arah celah terlebar, bukan +85° yang salah
    const treeDist=140; // cukup jauh dari pusat node agar tidak nimpa jalan
    nodeTrees.push({nodeId:node.id,
      x:node.x+Math.cos(trad)*treeDist,
      y:node.y+Math.sin(trad)*treeDist,
      size:17,type:['pine','round','palm'][node.id%3]});
  });

  return {nodes,edges,adj,cc,nodeBuildings,nodeTrees,lakes};
}

// ============================================================
// BFS & DIJKSTRA
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
  // total weight (untuk Dijkstra — sudah termasuk faktor tipe jalan)
  let t=0;
  for(let i=0;i<path.length-1;i++){
    const nb=adj[path[i]]?.find(n=>n.to===path[i+1]);
    if(nb)t+=nb.weight;
  }
  return t;
}
function pathKm(path,adj){
  // total jarak nyata dalam km (pakai dist, bukan weight)
  let t=0;
  for(let i=0;i<path.length-1;i++){
    const nb=adj[path[i]]?.find(n=>n.to===path[i+1]);
    if(nb)t+=(nb.dist||nb.weight); // fallback ke weight jika dist tidak ada
  }
  return (t/400).toFixed(2);
}

// ============================================================
// CANVAS
// ============================================================
const mc=document.getElementById('mc');
const ctx=mc.getContext('2d');
mc.width=MAP_W; mc.height=MAP_H;

// ============================================================
// DRAW BUILDING  (detailed per-type icons)
// ============================================================
function drawBuilding(ctx,b){
  ctx.save();
  ctx.shadowBlur=10; ctx.shadowOffsetX=3; ctx.shadowOffsetY=4;
  ctx.shadowColor='rgba(0,0,0,0.20)';
  ctx.fillStyle=C.building;
  ctx.beginPath(); ctx.roundRect(b.x,b.y,b.width,b.height,3); ctx.fill();
  ctx.shadowBlur=0; ctx.shadowOffsetX=0; ctx.shadowOffsetY=0;
  ctx.strokeStyle='rgba(130,110,90,0.55)'; ctx.lineWidth=1.4; ctx.stroke();

  const cx=b.x+b.width/2, cy=b.y+b.height/2;

  if(b.type==='school'){
    ctx.fillStyle='#c0604a';
    ctx.beginPath(); ctx.moveTo(b.x-4,b.y); ctx.lineTo(cx,b.y-16); ctx.lineTo(b.x+b.width+4,b.y); ctx.fill();
    ctx.fillStyle='#90caf9';
    for(let i=0;i<3;i++) ctx.fillRect(b.x+9+i*21,b.y+12,8,14);
    ctx.fillStyle='#6d4c41'; ctx.fillRect(cx-5,b.y+b.height-14,10,14);

  }else if(b.type==='airport'){
    ctx.fillStyle='#90a4ae'; ctx.fillRect(b.x,b.y-10,b.width,10);
    ctx.fillStyle='#607d8b'; ctx.fillRect(b.x+b.width-16,b.y-28,10,32);
    ctx.fillStyle='#80cbc4';
    ctx.beginPath(); ctx.arc(b.x+b.width-11,b.y-30,8,0,Math.PI*2); ctx.fill();
    ctx.fillStyle='#b3e5fc';
    for(let i=0;i<5;i++) ctx.fillRect(b.x+6+i*15,b.y+8,8,10);

  }else if(b.type==='mall'){
    ctx.fillStyle='#78909c'; ctx.fillRect(b.x,b.y-8,b.width,8);
    for(let i=0;i<4;i++){
      ctx.fillStyle=i%2===0?'#b3e5fc':'#e1f5fe';
      ctx.fillRect(b.x+7+i*17,b.y+10,10,20);
    }
    ctx.fillStyle='#e53935'; ctx.fillRect(cx-12,b.y-18,24,8);
    ctx.fillStyle='white'; ctx.font='bold 6px Inter,sans-serif';
    ctx.textAlign='center'; ctx.textBaseline='middle';
    ctx.fillText('MALL',cx,b.y-14);

  }else if(b.type==='hospital'){
    ctx.fillStyle='#e53935';
    ctx.fillRect(cx-5,b.y+8,10,24); ctx.fillRect(cx-16,b.y+17,32,7);
    ctx.fillStyle='#b3e5fc';
    ctx.fillRect(b.x+6,b.y+8,8,10); ctx.fillRect(b.x+b.width-14,b.y+8,8,10);
    ctx.strokeStyle='#4caf50'; ctx.lineWidth=2;
    ctx.beginPath(); ctx.arc(cx,b.y-6,8,0,Math.PI*2); ctx.stroke();
    ctx.fillStyle='rgba(76,175,80,0.25)';
    ctx.beginPath(); ctx.arc(cx,b.y-6,7,0,Math.PI*2); ctx.fill();
    ctx.fillStyle='#2e7d32'; ctx.font='8px sans-serif';
    ctx.textAlign='center'; ctx.textBaseline='middle'; ctx.fillText('H',cx,b.y-6);

  }else if(b.type==='mosque'){
    const gd=ctx.createRadialGradient(cx-4,b.y-18,1,cx,b.y-10,22);
    gd.addColorStop(0,'#fff9c4'); gd.addColorStop(1,'#f9a825');
    ctx.fillStyle=gd;
    ctx.beginPath(); ctx.arc(cx,b.y-10,22,Math.PI,0,true); ctx.fill();
    ctx.fillStyle='#795548';
    ctx.fillRect(b.x+3,b.y-22,7,26); ctx.fillRect(b.x+b.width-10,b.y-22,7,26);
    ctx.fillStyle='#fdd835';
    ctx.beginPath(); ctx.arc(b.x+6,b.y-24,5,0,Math.PI*2); ctx.fill();
    ctx.beginPath(); ctx.arc(b.x+b.width-7,b.y-24,5,0,Math.PI*2); ctx.fill();
    ctx.fillStyle='#f57f17'; ctx.font='11px sans-serif';
    ctx.textAlign='center'; ctx.textBaseline='middle'; ctx.fillText('☽',cx,b.y-30);

  }else if(b.type==='hotel'){
    ctx.strokeStyle='#90a4ae'; ctx.lineWidth=1.5;
    ctx.beginPath(); ctx.moveTo(cx,b.y-24); ctx.lineTo(cx,b.y); ctx.stroke();
    ctx.fillStyle='#e53935'; ctx.fillRect(cx,b.y-24,12,7);
    for(let r=0;r<2;r++) for(let c=0;c<3;c++){
      ctx.fillStyle='#b3e5fc';
      ctx.fillRect(b.x+8+c*17,b.y+10+r*18,10,12);
    }

  }else if(b.type==='office'){
    for(let r=0;r<3;r++) for(let c=0;c<3;c++){
      ctx.fillStyle=r===0?'#c8e6c9':(r===1?'#a5d6a7':'#81c784');
      ctx.fillRect(b.x+7+c*18,b.y+6+r*13,12,9);
    }
    ctx.fillStyle='#5c6bc0'; ctx.fillRect(cx-7,b.y+b.height-14,14,14);

  }else if(b.type==='gasstation'){
    ctx.fillStyle='#f9a825'; ctx.fillRect(b.x-8,b.y-6,b.width+16,8);
    ctx.strokeStyle='#e65100'; ctx.lineWidth=1.5; ctx.strokeRect(b.x-8,b.y-6,b.width+16,8);
    ctx.fillStyle='#546e7a'; ctx.fillRect(cx-6,b.y+6,12,22);
    ctx.fillStyle='#ff5722'; ctx.fillRect(cx-4,b.y+8,8,6);
    ctx.fillStyle='#e53935';
    ctx.beginPath(); ctx.arc(b.x+10,b.y-14,9,0,Math.PI*2); ctx.fill();
    ctx.fillStyle='white'; ctx.font='bold 7px Inter,sans-serif';
    ctx.textAlign='center'; ctx.textBaseline='middle'; ctx.fillText('SPBU',b.x+10,b.y-14);

  }else if(b.type==='university'){
    ctx.fillStyle='#8d6e63';
    ctx.beginPath(); ctx.moveTo(b.x-6,b.y); ctx.lineTo(cx,b.y-18); ctx.lineTo(b.x+b.width+6,b.y); ctx.fill();
    for(let i=0;i<5;i++){
      ctx.fillStyle='#efebe9';
      ctx.fillRect(b.x+6+i*14,b.y,6,b.height);
    }

  }else if(b.type==='station'){
    ctx.fillStyle='#455a64'; ctx.fillRect(b.x,b.y-8,b.width,10);
    ctx.fillStyle='#78909c'; ctx.fillRect(b.x+8,b.y+14,b.width-16,18);
    ctx.strokeStyle='#b0bec5'; ctx.lineWidth=2;
    for(let t=0;t<5;t++){
      ctx.beginPath(); ctx.moveTo(b.x+10+t*10,b.y+14); ctx.lineTo(b.x+10+t*10,b.y+32); ctx.stroke();
    }

  }else if(b.type==='museum'){
    ctx.fillStyle='#7b1fa2';
    ctx.beginPath(); ctx.moveTo(b.x-5,b.y-10); ctx.lineTo(cx,b.y-26); ctx.lineTo(b.x+b.width+5,b.y-10); ctx.fill();
    ctx.fillStyle='#9c27b0'; ctx.fillRect(b.x,b.y-10,b.width,10);
    for(let i=0;i<4;i++){
      ctx.fillStyle='#f3e5f5'; ctx.fillRect(b.x+8+i*16,b.y,7,b.height);
    }

  }else{
    ctx.fillStyle='#9e9e9e';
    ctx.beginPath(); ctx.moveTo(b.x,b.y); ctx.lineTo(cx,b.y-12); ctx.lineTo(b.x+b.width,b.y); ctx.fill();
    ctx.fillStyle='#b3e5fc';
    ctx.fillRect(b.x+8,b.y+8,b.width-16,b.height-16);
  }
  ctx.restore();
}

// ============================================================
// DRAW TREE
// ============================================================
function drawTree(ctx,t){
  ctx.save();
  if(t.type==='pine'){
    [[0,'#1b5e20',0.55],[t.size*0.35,'#2e7d32',0.72],[t.size*0.62,'#388e3c',0.9]].forEach(([dy,col,sc])=>{
      ctx.fillStyle=col;
      ctx.beginPath();
      ctx.moveTo(t.x,t.y-t.size*1.05+dy);
      ctx.lineTo(t.x-t.size*sc,t.y+dy);
      ctx.lineTo(t.x+t.size*sc,t.y+dy);
      ctx.fill();
    });
    ctx.fillStyle='#5d4037'; ctx.fillRect(t.x-2.5,t.y+1,5,6);

  }else if(t.type==='palm'){
    ctx.strokeStyle='#8d6e63'; ctx.lineWidth=3.5; ctx.lineCap='round';
    ctx.beginPath(); ctx.moveTo(t.x,t.y+5);
    ctx.quadraticCurveTo(t.x+6,t.y-t.size*0.5,t.x+3,t.y-t.size);
    ctx.stroke();
    ctx.strokeStyle='#558b2f'; ctx.lineWidth=2.5;
    for(let i=0;i<6;i++){
      const ang=(i/6)*Math.PI*2-Math.PI/2;
      ctx.beginPath();
      ctx.moveTo(t.x+3,t.y-t.size);
      ctx.quadraticCurveTo(
        t.x+3+Math.cos(ang)*t.size*0.65, t.y-t.size+Math.sin(ang)*t.size*0.45,
        t.x+3+Math.cos(ang)*t.size,      t.y-t.size*0.55+Math.sin(ang)*t.size*0.85
      );
      ctx.stroke();
    }
    ctx.fillStyle='#a5783a';
    for(let i=0;i<3;i++){
      const ang=(i/3)*Math.PI*2;
      ctx.beginPath(); ctx.arc(t.x+3+Math.cos(ang)*4,t.y-t.size+Math.sin(ang)*4,4,0,Math.PI*2); ctx.fill();
    }

  }else{
    ctx.fillStyle='rgba(0,0,0,0.10)';
    ctx.beginPath(); ctx.ellipse(t.x+4,t.y-t.size/2+5,t.size/2+2,t.size/3,0,0,Math.PI*2); ctx.fill();
    const g=ctx.createRadialGradient(t.x-3,t.y-t.size/2-3,1,t.x,t.y-t.size/2,t.size/2+1);
    g.addColorStop(0,'#c8e6c9'); g.addColorStop(0.5,'#66bb6a'); g.addColorStop(1,'#2e7d32');
    ctx.fillStyle=g;
    ctx.beginPath(); ctx.arc(t.x,t.y-t.size/2,t.size/2+1,0,Math.PI*2); ctx.fill();
    ctx.fillStyle='#5d4037'; ctx.fillRect(t.x-2.5,t.y-3,5,7);
  }
  ctx.restore();
}

// ============================================================
// DRAW LAKE
// ============================================================
function drawLake(ctx,lake){
  ctx.save();
  ctx.fillStyle='#a8c8b0';
  ctx.beginPath(); ctx.ellipse(lake.cx,lake.cy,lake.rx+8,lake.ry+6,0,0,Math.PI*2); ctx.fill();
  const gw=ctx.createRadialGradient(lake.cx-lake.rx*0.2,lake.cy-lake.ry*0.2,4,
                                     lake.cx,lake.cy,Math.max(lake.rx,lake.ry));
  gw.addColorStop(0,'#cce8f4');
  gw.addColorStop(0.45,'#64b5d6');
  gw.addColorStop(1,'#2980b9');
  ctx.fillStyle=gw;
  ctx.beginPath(); ctx.ellipse(lake.cx,lake.cy,lake.rx,lake.ry,0,0,Math.PI*2); ctx.fill();
  const gs=ctx.createRadialGradient(lake.cx-lake.rx*0.3,lake.cy-lake.ry*0.3,1,
                                     lake.cx-lake.rx*0.3,lake.cy-lake.ry*0.3,lake.rx*0.5);
  gs.addColorStop(0,'rgba(255,255,255,0.45)');
  gs.addColorStop(1,'rgba(255,255,255,0)');
  ctx.fillStyle=gs;
  ctx.beginPath(); ctx.ellipse(lake.cx-lake.rx*0.2,lake.cy-lake.ry*0.25,lake.rx*0.42,lake.ry*0.28,0,0,Math.PI*2); ctx.fill();
  ctx.strokeStyle='rgba(255,255,255,0.18)'; ctx.lineWidth=1;
  for(let r=1;r<=3;r++){
    ctx.beginPath();
    ctx.ellipse(lake.cx+r*3,lake.cy,lake.rx*(0.25+r*0.2),lake.ry*(0.25+r*0.2),0,0,Math.PI*2);
    ctx.stroke();
  }
  ctx.strokeStyle='rgba(40,130,190,0.5)'; ctx.lineWidth=2;
  ctx.beginPath(); ctx.ellipse(lake.cx,lake.cy,lake.rx,lake.ry,0,0,Math.PI*2); ctx.stroke();
  ctx.fillStyle='rgba(10,60,120,0.75)';
  ctx.font='italic 11px Georgia,serif';
  ctx.textAlign='center'; ctx.textBaseline='middle';
  ctx.fillText(lake.label,lake.cx,lake.cy+2);
  ctx.restore();
}

// ============================================================
// DRAW MAP BACKGROUND  — DIPERBAIKI KONTRAST (warna lebih terang, zona lebih tipis)
// ============================================================
function drawBackground(ctx){
  // ── 1. BASE LAND: gradien terang ──
  const lg=ctx.createLinearGradient(0,0,MAP_W,MAP_H);
  lg.addColorStop(0,'#faf6e8');
  lg.addColorStop(0.5,'#f5efdf');
  lg.addColorStop(1,'#efe7d4');
  ctx.fillStyle=lg;
  ctx.fillRect(0,0,MAP_W,MAP_H);

  // ── 1b. GRASS PATCHES: bercak rumput hijau tersebar tipis (vibe gurun + sedikit hijau) ──
  const grassPatches=[
    {cx:210,          cy:180,          rx:130,ry:90,  rot:-0.3},
    {cx:MAP_W-190,    cy:220,          rx:110,ry:80,  rot:0.4},
    {cx:180,          cy:MAP_H-200,    rx:140,ry:95,  rot:0.2},
    {cx:MAP_W-230,    cy:MAP_H-180,    rx:125,ry:85,  rot:-0.2},
    {cx:MAP_W*0.42,   cy:150,          rx:105,ry:60,  rot:0.1},
    {cx:MAP_W*0.72,   cy:MAP_H*0.15,   rx:90, ry:65,  rot:-0.25},
    {cx:MAP_W*0.28,   cy:MAP_H*0.88,   rx:115,ry:70,  rot:0.15},
    {cx:MAP_W*0.60,   cy:MAP_H*0.92,   rx:100,ry:65,  rot:-0.1},
    {cx:MAP_W*0.04,   cy:MAP_H*0.50,   rx:80, ry:120, rot:0.3},
    {cx:MAP_W*0.97,   cy:MAP_H*0.55,   rx:75, ry:110, rot:-0.2},
    {cx:MAP_W*0.35,   cy:MAP_H*0.42,   rx:55, ry:40,  rot:0.5},
    {cx:MAP_W*0.80,   cy:MAP_H*0.65,   rx:60, ry:42,  rot:-0.4},
    {cx:MAP_W*0.15,   cy:MAP_H*0.65,   rx:50, ry:38,  rot:0.2},
  ];
  grassPatches.forEach(p=>{
    ctx.save();
    ctx.translate(p.cx,p.cy);
    ctx.rotate(p.rot||0);
    const go=ctx.createRadialGradient(0,-p.ry*0.2,4,0,0,Math.max(p.rx,p.ry));
    go.addColorStop(0,'rgba(130,185,80,0.22)');
    go.addColorStop(0.6,'rgba(100,160,55,0.14)');
    go.addColorStop(1,'rgba(80,140,40,0.0)');
    ctx.fillStyle=go;
    ctx.beginPath(); ctx.ellipse(0,0,p.rx,p.ry,0,0,Math.PI*2); ctx.fill();
    const gi=ctx.createRadialGradient(-p.rx*0.1,-p.ry*0.1,2,0,0,Math.max(p.rx,p.ry)*0.55);
    gi.addColorStop(0,'rgba(145,195,75,0.20)');
    gi.addColorStop(1,'rgba(110,165,50,0.05)');
    ctx.fillStyle=gi;
    ctx.beginPath(); ctx.ellipse(0,0,p.rx*0.65,p.ry*0.65,0,0,Math.PI*2); ctx.fill();
    ctx.restore();
  });

  // ── 2. URBAN BLOCK GRID: zona dengan opasitas sangat tipis agar jalan abu-abu kontras ──
  const residentialZones=[
    {x:120,y:120,w:380,h:260},
    {x:600,y:80,w:310,h:200},
    {x:1800,y:90,w:340,h:230},
    {x:2200,y:200,w:380,h:280},
    {x:80,y:1300,w:320,h:320},
    {x:500,y:1500,w:280,h:220},
    {x:1600,y:1400,w:420,h:280},
    {x:2300,y:1400,w:300,h:300},
  ];
  residentialZones.forEach(z=>{
    ctx.save();
    ctx.fillStyle='rgba(255,245,160,0.1)';   // lebih tipis
    ctx.beginPath();
    ctx.roundRect(z.x,z.y,z.w,z.h,12);
    ctx.fill();
    ctx.strokeStyle='rgba(200,175,80,0.08)';
    ctx.lineWidth=1;
    ctx.stroke();
    ctx.restore();
  });

  const commercialZones=[
    {x:950,y:130,w:350,h:240},
    {x:1350,y:80,w:380,h:200},
    {x:900,y:1450,w:420,h:240},
    {x:2050,y:1300,w:340,h:280},
  ];
  commercialZones.forEach(z=>{
    ctx.save();
    ctx.fillStyle='rgba(170,210,250,0.1)';
    ctx.beginPath();
    ctx.roundRect(z.x,z.y,z.w,z.h,12);
    ctx.fill();
    ctx.strokeStyle='rgba(80,140,200,0.08)';
    ctx.lineWidth=1;
    ctx.stroke();
    ctx.restore();
  });

  const industrialZones=[
    {x:2000,y:800,w:580,h:300},
    {x:2100,y:500,w:420,h:260},
  ];
  industrialZones.forEach(z=>{
    ctx.save();
    ctx.fillStyle='rgba(160,160,160,0.1)';
    ctx.beginPath();
    ctx.roundRect(z.x,z.y,z.w,z.h,8);
    ctx.fill();
    ctx.strokeStyle='rgba(130,130,130,0.08)';
    ctx.lineWidth=1;
    ctx.stroke();
    ctx.restore();
  });

  // ── 3. TAMAN KOTA: hijau tipis ──
  const parks=[
    {cx:MAP_W*0.08, cy:MAP_H*0.82, rx:170,ry:130},
    {cx:MAP_W*0.92, cy:MAP_H*0.12, rx:150,ry:110},
    {cx:MAP_W*0.48, cy:MAP_H*0.05, rx:200,ry:90},
    {cx:MAP_W*0.78, cy:MAP_H*0.88, rx:160,ry:130},
    {cx:MAP_W*0.22, cy:MAP_H*0.18, rx:130,ry:100},
  ];
  parks.forEach(p=>{
    ctx.save();
    const gr=ctx.createRadialGradient(p.cx-p.rx*0.2,p.cy-p.ry*0.2,5,p.cx,p.cy,Math.max(p.rx,p.ry));
    gr.addColorStop(0,'rgba(110,180,80,0.15)');
    gr.addColorStop(1,'rgba(70,135,50,0.05)');
    ctx.fillStyle=gr;
    ctx.beginPath();
    ctx.ellipse(p.cx,p.cy,p.rx,p.ry,0,0,Math.PI*2);
    ctx.fill();
    ctx.strokeStyle='rgba(70,140,50,0.12)';
    ctx.lineWidth=1.5;
    ctx.setLineDash([6,4]);
    ctx.stroke();
    ctx.setLineDash([]);
    ctx.restore();
  });

  // ── 4. TROTOAR / SIDEWALK GRID (sangat tipis) ──
  ctx.save();
  ctx.strokeStyle='rgba(150,138,118,0.12)';
  ctx.lineWidth=1;
  const gridSpacingY=95, gridSpacingX=110;
  for(let y=gridSpacingY;y<MAP_H;y+=gridSpacingY){
    ctx.beginPath();
    ctx.moveTo(0,y);
    ctx.lineTo(MAP_W,y);
    ctx.stroke();
  }
  for(let x=gridSpacingX;x<MAP_W;x+=gridSpacingX){
    ctx.beginPath();
    ctx.moveTo(x,0);
    ctx.lineTo(x,MAP_H);
    ctx.stroke();
  }
  ctx.restore();

  // ── 5. BLOK BANGUNAN MINI (sangat tipis) ──
  const blockRnd=mkRnd(0xabc123);
  for(let row=0;row<MAP_H;row+=95){
    for(let col=0;col<MAP_W;col+=110){
      if(blockRnd()<0.45){
        const bw=12+blockRnd()*28;
        const bh=10+blockRnd()*22;
        const bx=col+15+blockRnd()*(110-bw-30);
        const by=row+12+blockRnd()*(95-bh-25);
        ctx.save();
        ctx.fillStyle='rgba(130,110,90,0.2)';
        ctx.shadowBlur=2;
        ctx.beginPath();
        ctx.roundRect(bx,by,bw,bh,2);
        ctx.fill();
        ctx.restore();
      }
    }
  }

  // ── 6. VIGNETTE ──
  const vig=ctx.createRadialGradient(MAP_W/2,MAP_H/2,MAP_W*0.25,MAP_W/2,MAP_H/2,MAP_W*0.85);
  vig.addColorStop(0,'rgba(0,0,0,0)');
  vig.addColorStop(1,'rgba(0,0,0,0.05)');
  ctx.fillStyle=vig;
  ctx.fillRect(0,0,MAP_W,MAP_H);

  // ── 7. WATERWAY tipis ──
  ctx.save();
  ctx.strokeStyle='rgba(100,185,220,0.5)';
  ctx.lineWidth=5;
  ctx.lineCap='round';
  ctx.beginPath();
  ctx.moveTo(0,MAP_H*0.31);
  ctx.bezierCurveTo(MAP_W*0.12,MAP_H*0.28, MAP_W*0.22,MAP_H*0.34, MAP_W*0.34,MAP_H*0.30);
  ctx.bezierCurveTo(MAP_W*0.40,MAP_H*0.27, MAP_W*0.44,MAP_H*0.33, MAP_W*0.46,MAP_H*0.29);
  ctx.stroke();
  ctx.beginPath();
  ctx.moveTo(MAP_W*0.62,MAP_H*0.52);
  ctx.bezierCurveTo(MAP_W*0.70,MAP_H*0.58, MAP_W*0.78,MAP_H*0.64, MAP_W*0.84,MAP_H*0.72);
  ctx.bezierCurveTo(MAP_W*0.88,MAP_H*0.77, MAP_W*0.92,MAP_H*0.80, MAP_W*0.96,MAP_H*0.84);
  ctx.stroke();
  ctx.restore();

  // ── 8. LEGENDA ZONA ──
  const legendX=30, legendY=MAP_H-100;
  const legendItems=[
    {color:'rgba(255,245,120,0.4)',label:'Perumahan'},
    {color:'rgba(140,195,255,0.4)',label:'Komersial'},
    {color:'rgba(160,160,160,0.35)',label:'Industri'},
    {color:'rgba(100,185,90,0.35)',label:'Taman'},
  ];
  ctx.save();
  ctx.fillStyle='rgba(255,255,245,0.85)';
  ctx.beginPath();
  ctx.roundRect(legendX-8,legendY-12,145,75,8);
  ctx.fill();
  ctx.strokeStyle='rgba(150,130,100,0.3)';
  ctx.lineWidth=1;
  ctx.stroke();
  ctx.font='bold 9px Georgia,serif';
  ctx.fillStyle='rgba(60,45,30,0.9)';
  ctx.fillText('LEGENDA ZONA',legendX,legendY+2);
  legendItems.forEach((item,i)=>{
    const ly=legendY+16+i*14;
    ctx.fillStyle=item.color;
    ctx.beginPath();
    ctx.roundRect(legendX,ly,14,10,2);
    ctx.fill();
    ctx.strokeStyle='rgba(100,80,60,0.3)';
    ctx.lineWidth=0.8;
    ctx.stroke();
    ctx.fillStyle='rgba(60,45,30,0.85)';
    ctx.font='8.5px Georgia,serif';
    ctx.fillText(item.label,legendX+18,ly+8);
  });
  ctx.restore();

  // ── 9. BORDER PETA ──
  ctx.save();
  const borderGrad=ctx.createLinearGradient(0,0,MAP_W,MAP_H);
  borderGrad.addColorStop(0,'rgba(100,75,45,0.4)');
  borderGrad.addColorStop(1,'rgba(80,60,40,0.35)');
  ctx.strokeStyle=borderGrad;
  ctx.lineWidth=12;
  ctx.strokeRect(6,6,MAP_W-12,MAP_H-12);
  ctx.strokeStyle='rgba(90,70,45,0.25)';
  ctx.lineWidth=3;
  ctx.strokeRect(16,16,MAP_W-32,MAP_H-32);
  const corners=[[22,22,0],[MAP_W-22,22,Math.PI/2],[MAP_W-22,MAP_H-22,Math.PI],[22,MAP_H-22,3*Math.PI/2]];
  corners.forEach(([cx,cy,angle])=>{
    ctx.save();
    ctx.translate(cx,cy);
    ctx.rotate(angle);
    ctx.strokeStyle='rgba(100,75,45,0.5)';
    ctx.lineWidth=2;
    ctx.beginPath();
    ctx.moveTo(0,0); ctx.lineTo(20,0);
    ctx.moveTo(0,0); ctx.lineTo(0,20);
    ctx.stroke();
    ctx.restore();
  });
  ctx.restore();
}

// ============================================================
// MAIN DRAW
// ============================================================
function draw(bPath=[],dPath=[],tBFS=null,tDijk=null){
  ctx.clearRect(0,0,MAP_W,MAP_H);
  drawBackground(ctx);

  S.lakes.forEach(l=>drawLake(ctx,l));

  // ── Roads: border/kerb (warna abu gelap) ──
  S.edges.forEach(e=>{
    if(e.bypass) return; // bypass digambar terpisah
    const a=S.nodes[e.from],b=S.nodes[e.to];
    const k=`${e.from}-${e.to}`;
    const {cp1,cp2}=S.cc[k]||getCP(a,b);
    const [fw,bw]=roadW(e);
    const isHW=fw>=24;
    ctx.save();
    ctx.shadowBlur=6; ctx.shadowOffsetX=2; ctx.shadowOffsetY=2;
    ctx.shadowColor='rgba(0,0,0,0.2)';
    ctx.beginPath(); ctx.moveTo(a.x,a.y);
    ctx.bezierCurveTo(cp1.x,cp1.y,cp2.x,cp2.y,b.x,b.y);
    ctx.strokeStyle=isHW?C.hwBorder:(fw>=20?C.mainBorder:C.sideBorder);
    ctx.lineWidth=bw; ctx.lineCap='round'; ctx.stroke();
    ctx.restore();
  });

  // ── Bypass edges: jalan lingkar melengkung keluar ──
  S.edges.filter(e=>e.bypass).forEach(e=>{
    const a=S.nodes[e.from],b=S.nodes[e.to];
    const k=`${e.from}-${e.to}`;
    const {cp1,cp2}=S.cc[k]||getCPBypass(a,b);
    ctx.save();
    // Border
    ctx.shadowBlur=5; ctx.shadowColor='rgba(0,0,0,0.18)';
    ctx.beginPath(); ctx.moveTo(a.x,a.y);
    ctx.bezierCurveTo(cp1.x,cp1.y,cp2.x,cp2.y,b.x,b.y);
    ctx.strokeStyle='#5a5a5a'; ctx.lineWidth=18; ctx.lineCap='round'; ctx.stroke();
    ctx.shadowBlur=0;
    // Surface
    ctx.beginPath(); ctx.moveTo(a.x,a.y);
    ctx.bezierCurveTo(cp1.x,cp1.y,cp2.x,cp2.y,b.x,b.y);
    ctx.strokeStyle='#b8b0a0'; ctx.lineWidth=14; ctx.lineCap='round'; ctx.stroke();
    // Garis putus tengah — tanda jalan bypass
    ctx.setLineDash([18,12]);
    ctx.beginPath(); ctx.moveTo(a.x,a.y);
    ctx.bezierCurveTo(cp1.x,cp1.y,cp2.x,cp2.y,b.x,b.y);
    ctx.strokeStyle='rgba(255,240,160,0.7)'; ctx.lineWidth=2; ctx.stroke();
    ctx.setLineDash([]);
    ctx.restore();
  });

  // ── Roads: surface pass (warna abu terang) ──
  S.edges.forEach(e=>{
    const a=S.nodes[e.from],b=S.nodes[e.to];
    const k=`${e.from}-${e.to}`;
    const {cp1,cp2}=S.cc[k]||getCP(a,b);
    const [fw]=roadW(e);
    const isHW=fw>=24;
    ctx.beginPath(); ctx.moveTo(a.x,a.y);
    ctx.bezierCurveTo(cp1.x,cp1.y,cp2.x,cp2.y,b.x,b.y);
    ctx.strokeStyle=isHW?C.hwFill:(fw>=20?C.mainFill:C.sideFill);
    ctx.lineWidth=fw; ctx.lineCap='round'; ctx.stroke();
  });

  // ── Road centre markings (lebih kontras) ──
  S.edges.forEach(e=>{
    const t=edgeType(e);
    if(t>1)return;
    const a=S.nodes[e.from],b=S.nodes[e.to];
    const k=`${e.from}-${e.to}`;
    const {cp1,cp2}=S.cc[k]||getCP(a,b);
    ctx.save();
    if(t===0){
      ctx.setLineDash([14,11]);
      ctx.strokeStyle='rgba(255,235,160,0.85)'; ctx.lineWidth=2.5;
    }else{
      ctx.setLineDash([8,8]);
      ctx.strokeStyle='rgba(255,245,180,0.7)'; ctx.lineWidth=1.8;
    }
    ctx.beginPath(); ctx.moveTo(a.x,a.y);
    ctx.bezierCurveTo(cp1.x,cp1.y,cp2.x,cp2.y,b.x,b.y);
    ctx.stroke(); ctx.setLineDash([]); ctx.restore();
  });

  // ── Label jarak km DI SAMPING jalan (tegak lurus, teks horizontal) ──
  S.edges.forEach(e=>{
    const a=S.nodes[e.from],b=S.nodes[e.to];
    const k=`${e.from}-${e.to}`;
    const {cp1,cp2}=S.cc[k]||getCP(a,b);
    // Titik tengah bezier
    const mp=bez3(0.5,a,cp1,cp2,b);
    // Arah tangent di titik tengah
    const p1=bez3(0.47,a,cp1,cp2,b);
    const p2=bez3(0.53,a,cp1,cp2,b);
    const tang=Math.atan2(p2.y-p1.y,p2.x-p1.x);
    // Tegak lurus ke kiri jalan (arah -90° dari tangent)
    const perp=tang-Math.PI/2;
    const offDist=26; // px offset dari sumbu jalan
    const lx=mp.x+Math.cos(perp)*offDist;
    const ly=mp.y+Math.sin(perp)*offDist;

    const km=(e.dist/400).toFixed(2);
    const lbl=`${km} km`;

    // Warna badge sesuai jarak: hijau=dekat, kuning=sedang, merah=jauh
    const w=e.weight;
    let bgCol,txtCol,borderCol;
    if(w<300){      bgCol='rgba(220,255,220,0.94)';borderCol='#4caf50';txtCol='#1b5e20';}
    else if(w<600){ bgCol='rgba(255,248,210,0.94)';borderCol='#f9a825';txtCol='#5f3c00';}
    else{            bgCol='rgba(255,220,215,0.94)';borderCol='#e53935';txtCol='#7f0000';}

    ctx.save();
    ctx.font='bold 12px Inter,sans-serif';
    const tw=ctx.measureText(lbl).width;
    const pw=tw+12,ph=17,pr=5;
    // Garis kecil penghubung ke jalan
    ctx.strokeStyle='rgba(120,110,90,0.4)';
    ctx.lineWidth=1;
    ctx.setLineDash([3,3]);
    ctx.beginPath();
    ctx.moveTo(mp.x,mp.y);
    ctx.lineTo(lx,ly);
    ctx.stroke();
    ctx.setLineDash([]);
    // Badge
    ctx.shadowBlur=5; ctx.shadowColor='rgba(0,0,0,0.18)';
    ctx.fillStyle=bgCol;
    ctx.strokeStyle=borderCol;
    ctx.lineWidth=1.5;
    ctx.beginPath();
    ctx.roundRect(lx-pw/2,ly-ph/2,pw,ph,pr);
    ctx.fill(); ctx.stroke();
    ctx.shadowBlur=0;
    // Teks
    ctx.fillStyle=txtCol;
    ctx.textAlign='center'; ctx.textBaseline='middle';
    ctx.fillText(lbl,lx,ly);
    ctx.restore();
  });

  // ── Intersection discs (disesuaikan dengan lebar jalan) ──
  S.nodes.forEach(n=>{
    let mw=6;
    S.edges.forEach(e=>{
      if(e.from===n.id||e.to===n.id){const[fw]=roadW(e);mw=Math.max(mw,fw);}
    });
    const isHW=mw>=24, r=mw/2+15;
    ctx.save();
    ctx.shadowBlur=6; ctx.shadowOffsetX=2; ctx.shadowOffsetY=2; ctx.shadowColor='rgba(0,0,0,0.2)';
    ctx.beginPath(); ctx.arc(n.x,n.y,r,0,Math.PI*2);
    ctx.fillStyle=isHW?C.hwBorder:C.mainBorder; ctx.fill();
    ctx.restore();
    ctx.beginPath(); ctx.arc(n.x,n.y,r-3,0,Math.PI*2);
    ctx.fillStyle=isHW?C.hwFill:C.mainFill; ctx.fill();
  });

  S.nodeBuildings.forEach(b=>drawBuilding(ctx,b));
  S.nodeTrees.forEach(t=>drawTree(ctx,t));

  // ── Route highlights ──
  function drawRoute(path,color,glow,lw,dash=[]){
    if(path.length<2)return;
    ctx.save();
    ctx.globalAlpha=0.35; ctx.shadowColor=glow; ctx.shadowBlur=22;
    for(let i=0;i<path.length-1;i++){
      const sg=S.cc[`${path[i]}-${path[i+1]}`]; if(!sg)continue;
      ctx.beginPath(); ctx.moveTo(sg.a.x,sg.a.y);
      ctx.bezierCurveTo(sg.cp1.x,sg.cp1.y,sg.cp2.x,sg.cp2.y,sg.b.x,sg.b.y);
      ctx.strokeStyle=color; ctx.lineWidth=lw+8; ctx.stroke();
    }
    ctx.globalAlpha=1; ctx.shadowBlur=0;
    for(let i=0;i<path.length-1;i++){
      const sg=S.cc[`${path[i]}-${path[i+1]}`]; if(!sg)continue;
      ctx.beginPath(); ctx.moveTo(sg.a.x,sg.a.y);
      ctx.bezierCurveTo(sg.cp1.x,sg.cp1.y,sg.cp2.x,sg.cp2.y,sg.b.x,sg.b.y);
      ctx.strokeStyle='rgba(255,255,255,0.95)'; ctx.lineWidth=lw+5; ctx.lineCap='round'; ctx.stroke();
    }
    ctx.setLineDash(dash);
    for(let i=0;i<path.length-1;i++){
      const sg=S.cc[`${path[i]}-${path[i+1]}`]; if(!sg)continue;
      ctx.beginPath(); ctx.moveTo(sg.a.x,sg.a.y);
      ctx.bezierCurveTo(sg.cp1.x,sg.cp1.y,sg.cp2.x,sg.cp2.y,sg.b.x,sg.b.y);
      ctx.strokeStyle=color; ctx.lineWidth=lw; ctx.lineCap='round'; ctx.stroke();
    }
    ctx.setLineDash([]); ctx.restore();
  }
  drawRoute(bPath,C.routeBFS,C.routeBFSGlow,8);
  drawRoute(dPath,C.routeDijk,C.routeDijkGlow,6,[10,6]);

  // ── Label jarak km di atas rute ──
  function drawKmLabel(path,color,offsetY){
    if(path.length<2)return;
    // Ambil titik tengah rute (segment tengah, t=0.5)
    const midSeg=S.cc[`${path[Math.floor((path.length-1)/2)]}-${path[Math.floor((path.length-1)/2)+1]}`];
    if(!midSeg)return;
    const mp=bez3(0.5,midSeg.a,midSeg.cp1,midSeg.cp2,midSeg.b);
    const km=pathKm(path,S.adj);
    const hops=path.length-1;
    const txt=`${km} km · ${hops} hop`;
    const tw=ctx.measureText(txt).width+20;
    ctx.save();
    // Badge background
    ctx.shadowBlur=8; ctx.shadowColor='rgba(0,0,0,0.25)';
    ctx.fillStyle='rgba(255,255,255,0.93)';
    ctx.strokeStyle=color; ctx.lineWidth=2;
    ctx.beginPath();
    ctx.roundRect(mp.x-tw/2, mp.y+offsetY-12, tw, 22, 6);
    ctx.fill(); ctx.stroke();
    ctx.shadowBlur=0;
    // Warna titik
    ctx.fillStyle=color;
    ctx.beginPath(); ctx.arc(mp.x-tw/2+10, mp.y+offsetY, 4, 0, Math.PI*2); ctx.fill();
    // Teks
    ctx.fillStyle='#1a1a1a';
    ctx.font='bold 11px Inter,sans-serif';
    ctx.textAlign='center'; ctx.textBaseline='middle';
    ctx.fillText(txt, mp.x+4, mp.y+offsetY);
    ctx.restore();
  }
  const algo=document.querySelector('input[name="algo"]:checked')?.value||'both';
  if(bPath.length>1) drawKmLabel(bPath,C.routeBFS,algo==='both'?-18:0);
  if(dPath.length>1) drawKmLabel(dPath,C.routeDijk,algo==='both'?6:0);
  S.nodes.forEach(n=>{
    const isS=n.id===S.startN,isE=n.id===S.endN;
    const onB=bPath.includes(n.id),onD=dPath.includes(n.id);
    if(isS||isE){
      ctx.save();
      ctx.shadowBlur=28; ctx.shadowColor=isS?'rgba(211,47,47,0.65)':'rgba(46,125,50,0.65)';
      ctx.beginPath(); ctx.arc(n.x,n.y,22,0,Math.PI*2);
      ctx.fillStyle='rgba(255,255,255,0.02)'; ctx.fill();
      ctx.restore();
    }
    const ng=ctx.createRadialGradient(n.x-3,n.y-3,1,n.x,n.y,18);
    ng.addColorStop(0,'#ffffff'); ng.addColorStop(1,'#f0ece4');
    ctx.save();
    ctx.shadowBlur=6; ctx.shadowOffsetX=1; ctx.shadowOffsetY=2; ctx.shadowColor='rgba(0,0,0,0.25)';
    ctx.beginPath(); ctx.arc(n.x,n.y,18,0,Math.PI*2);
    ctx.fillStyle=ng; ctx.fill();
    ctx.restore();
    ctx.strokeStyle=isS?'#c62828':isE?'#2e7d32':onD?C.routeDijk:onB?C.routeBFS:'#888';
    ctx.lineWidth=isS||isE?3:2; ctx.stroke();
    ctx.font='16px sans-serif'; ctx.textAlign='center'; ctx.textBaseline='middle';
    ctx.fillText(n.icon,n.x,n.y);
    if(isS||isE){
      ctx.font='24px sans-serif'; ctx.fillText(isS?'🚩':'🏁',n.x,n.y-26);
    }
    ctx.font='bold 10px Inter,sans-serif';
    const tw=ctx.measureText(n.label).width;
    ctx.save();
    ctx.shadowBlur=4; ctx.shadowOffsetY=1; ctx.shadowColor='rgba(0,0,0,0.2)';
    ctx.fillStyle='rgba(255,255,250,0.96)';
    ctx.beginPath(); ctx.roundRect(n.x-tw/2-6,n.y+20,tw+12,15,5); ctx.fill();
    ctx.restore();
    ctx.fillStyle=isS?'#b71c1c':isE?'#1b5e20':'#2c3e2f';
    ctx.fillText(n.label,n.x,n.y+28);
  });

  // ── Vehicles ──
  const algoV=document.querySelector('input[name="algo"]:checked')?.value||'both';
  const showBFS=(algoV==='both'||algoV==='bfs')&&bPath.length>1&&tBFS!==null;
  const showDijk=(algoV==='both'||algoV==='dijkstra')&&dPath.length>1&&tDijk!==null;

  function resolveVehiclePos(path,t){
    let totalLen=0,segs=[];
    for(let i=0;i<path.length-1;i++){
      const sg=S.cc[`${path[i]}-${path[i+1]}`];
      if(sg){segs.push(sg);totalLen+=sg.len;}
    }
    if(!totalLen)return null;
    const tgt=t*totalLen; let cum=0;
    for(const sg of segs){
      if(cum+sg.len>=tgt){
        const ls=tgt-cum,tv=arcLookup(sg.T,ls);
        const pt=bez3(tv,sg.a,sg.cp1,sg.cp2,sg.b);
        const tv2=Math.min(tv+0.006,1),pt2=bez3(tv2,sg.a,sg.cp1,sg.cp2,sg.b);
        return{px:pt.x,py:pt.y,ang:Math.atan2(pt2.y-pt.y,pt2.x-pt.x)};
      }
      cum+=sg.len;
    }
    return null;
  }

  function drawVehicle(px,py,ang,bodyCol,accentCol){
    ctx.save(); ctx.translate(px,py); ctx.rotate(ang);
    ctx.fillStyle='rgba(0,0,0,0.2)';
    ctx.beginPath(); ctx.ellipse(2,6,22,9,0,0,Math.PI*2); ctx.fill();
    const vg=ctx.createLinearGradient(-18,-9,-18,9);
    vg.addColorStop(0,lighten(bodyCol,50)); vg.addColorStop(1,bodyCol);
    ctx.fillStyle=vg;
    ctx.beginPath(); ctx.roundRect(-18,-8,36,16,5); ctx.fill();
    ctx.fillStyle=darken(bodyCol,25);
    ctx.beginPath(); ctx.roundRect(-10,-14,20,8,4); ctx.fill();
    ctx.fillStyle='rgba(200,235,255,0.85)';
    ctx.fillRect(-8,-13,7,5); ctx.fillRect(1,-13,7,5);
    ctx.fillStyle='#ffee58';
    ctx.beginPath(); ctx.ellipse(18,-5,4,3,0,0,Math.PI*2); ctx.fill();
    ctx.beginPath(); ctx.ellipse(18,5,4,3,0,0,Math.PI*2); ctx.fill();
    ctx.fillStyle='#ef5350';
    ctx.beginPath(); ctx.ellipse(-18,-5,3.5,2.5,0,0,Math.PI*2); ctx.fill();
    ctx.beginPath(); ctx.ellipse(-18,5,3.5,2.5,0,0,Math.PI*2); ctx.fill();
    [[-10,-8],[7,-8],[-10,6],[7,6]].forEach(([wx,wy])=>{
      ctx.fillStyle='#1e1e1e';
      ctx.beginPath(); ctx.ellipse(wx+1,wy+1,5,4,0,0,Math.PI*2); ctx.fill();
      ctx.strokeStyle='#888'; ctx.lineWidth=1; ctx.stroke();
    });
    ctx.fillStyle=accentCol;
    ctx.fillRect(-18,2,36,3);
    ctx.restore();
  }

  if(showBFS){const p=resolveVehiclePos(bPath,tBFS);if(p)drawVehicle(p.px,p.py,p.ang,'#bf360c','#ff8f00');}
  if(showDijk){const p=resolveVehiclePos(dPath,tDijk);if(p)drawVehicle(p.px,p.py,p.ang,'#0d47a1','#00b0ff');}

  updateMinimap(bPath,dPath);
}

function lighten(hex,a){
  const n=parseInt(hex.replace('#',''),16);
  return `rgb(${Math.min(255,(n>>16)+a)},${Math.min(255,((n>>8)&0xff)+a)},${Math.min(255,(n&0xff)+a)})`;
}
function darken(hex,a){
  const n=parseInt(hex.replace('#',''),16);
  return `rgb(${Math.max(0,(n>>16)-a)},${Math.max(0,((n>>8)&0xff)-a)},${Math.max(0,(n&0xff)-a)})`;
}

// ============================================================
// MINIMAP
// ============================================================
const mmc=document.getElementById('mmc');
const mmctx=mmc.getContext('2d');
const sx=MM_W/MAP_W,sy=MM_H/MAP_H;

function updateMinimap(bPath=[],dPath=[]){
  mmctx.clearRect(0,0,MM_W,MM_H);
  mmctx.fillStyle='#ede7db'; mmctx.fillRect(0,0,MM_W,MM_H);
  S.lakes.forEach(l=>{
    mmctx.fillStyle='#64b5d6';
    mmctx.beginPath(); mmctx.ellipse(l.cx*sx,l.cy*sy,l.rx*sx,l.ry*sy,0,0,Math.PI*2); mmctx.fill();
  });
  S.edges.forEach(e=>{
    const a=S.nodes[e.from],b=S.nodes[e.to];
    const {cp1,cp2}=getCP(a,b);
    const[fw]=roadW(e);
    mmctx.beginPath(); mmctx.moveTo(a.x*sx,a.y*sy);
    mmctx.bezierCurveTo(cp1.x*sx,cp1.y*sy,cp2.x*sx,cp2.y*sy,b.x*sx,b.y*sy);
    mmctx.strokeStyle=fw>=24?'#6a6a6a':'#8a8a8a';
    mmctx.lineWidth=fw>=24?2.2:1.5; mmctx.stroke();
  });
  if(bPath.length>1){
    mmctx.strokeStyle='rgba(230,81,0,0.9)'; mmctx.lineWidth=2.8;
    for(let i=0;i<bPath.length-1;i++){
      const sg=S.cc[`${bPath[i]}-${bPath[i+1]}`]; if(!sg)continue;
      mmctx.beginPath(); mmctx.moveTo(sg.a.x*sx,sg.a.y*sy);
      mmctx.bezierCurveTo(sg.cp1.x*sx,sg.cp1.y*sy,sg.cp2.x*sx,sg.cp2.y*sy,sg.b.x*sx,sg.b.y*sy);
      mmctx.stroke();
    }
  }
  S.nodes.forEach(n=>{
    mmctx.beginPath(); mmctx.arc(n.x*sx,n.y*sy,2.8,0,Math.PI*2);
    mmctx.fillStyle=n.id===S.startN?'#c62828':n.id===S.endN?'#2e7d32':'#555';
    mmctx.fill();
  });
  const vp=document.getElementById('vp');
  const vx=-S.px/S.zoom,vy=-S.py/S.zoom,vw=vp.clientWidth/S.zoom,vh=vp.clientHeight/S.zoom;
  const mv=document.getElementById('mmv');
  mv.style.left=Math.max(0,vx*sx)+'px'; mv.style.top=Math.max(0,vy*sy)+'px';
  mv.style.width=Math.min(vw*sx,MM_W)+'px'; mv.style.height=Math.min(vh*sy,MM_H)+'px';
}

// ============================================================
// TRANSFORM
// ============================================================
function applyXform(){
  document.getElementById('cvwrap').style.transform=`translate(${S.px}px,${S.py}px) scale(${S.zoom})`;
  document.getElementById('stZ').textContent=Math.round(S.zoom*100)+'%';
  document.getElementById('zhud').textContent='Zoom: '+Math.round(S.zoom*100)+'%';
  const realM=Math.round(55/S.zoom*100/10)*10;
  document.getElementById('sclbl').textContent=realM>=1000?(realM/1000).toFixed(1)+'km':realM+'m';
  document.getElementById('scline').style.width='100px';
  updateMinimap(S.bfsPath,S.dijkPath);
}
function zoomTo(z,cx,cy){
  const vp=document.getElementById('vp');
  cx=cx??vp.clientWidth/2; cy=cy??vp.clientHeight/2;
  const nz=Math.max(S.minZ,Math.min(S.maxZ,z));
  S.px=cx-(cx-S.px)*nz/S.zoom; S.py=cy-(cy-S.py)*nz/S.zoom;
  S.zoom=nz; applyXform();
}
function clampPan(){
  const vp=document.getElementById('vp');
  const margin=80;
  S.px=Math.min(margin,Math.max(vp.clientWidth-MAP_W*S.zoom-margin,S.px));
  S.py=Math.min(margin,Math.max(vp.clientHeight-MAP_H*S.zoom-margin,S.py));
}

// ============================================================
// UI (sama seperti asli, tidak diubah)
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
  // ── Ringkasan otomatis ──
  const sumBox=document.getElementById('rSummary');
  if(bP.length&&dP.length&&algo==='both'){
    const bKm=parseFloat(pathKm(bP,S.adj)), dKm=parseFloat(pathKm(dP,S.adj));
    const bH=bP.length-1, dH=dP.length-1;
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
    } else {
      html+=`<b style="color:#4a9eff">${kmWinner}</b> hemat <b>${kmDiff} km</b> &nbsp;·&nbsp; <b style="color:#4a9eff">${hopWinner}</b> hemat <b>${hopDiff} hop</b><br>
<span style="color:#6a7490;font-size:.65rem">BFS abaikan jarak → min singgah · Dijkstra hitung jarak → min km</span>`;
    }
    sumBox.innerHTML=html;
    sumBox.style.display='block';
  } else {
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
const sleep=ms=>new Promise(r=>setTimeout(r,ms));

function cameraFollowVehicle(pos){
  if(!S.camFollow||!pos)return;
  const vp=document.getElementById('vp');
  const tx=vp.clientWidth/2-pos.px*S.zoom,ty=vp.clientHeight/2-pos.py*S.zoom;
  S.px+=(tx-S.px)*0.06; S.py+=(ty-S.py)*0.06;
  clampPan(); applyXform();
}

function startTrack(autoStart=false){
  const algo=document.querySelector('input[name="algo"]:checked')?.value||'both';
  const hasB=(algo==='both'||algo==='bfs')&&S.bfsPath.length>1;
  const hasD=(algo==='both'||algo==='dijkstra')&&S.dijkPath.length>1;
  if(!hasB&&!hasD){if(!autoStart)notify('⚠️ Jalankan algoritma dulu');return;}
  S.trackActive=true;S.trackPaused=false;
  if(S.trackT>=1){S.trackT=0;S.trailBFS=[];S.trailDijk=[];}
  const btn=document.getElementById('btnTrack');
  btn.textContent='⏸ Pause';btn.className='hbtn act';
  if(autoStart)notify('🚗 Kendaraan mulai bergerak!');

  function resolvePos(path,t){
    let totalLen=0,segs=[];
    for(let i=0;i<path.length-1;i++){
      const sg=S.cc[`${path[i]}-${path[i+1]}`];
      if(sg){segs.push(sg);totalLen+=sg.len;}
    }
    if(!totalLen)return null;
    const tgt=t*totalLen;let cum=0;
    for(const sg of segs){
      if(cum+sg.len>=tgt){
        const ls=tgt-cum,tv=arcLookup(sg.T,ls);
        const pt=bez3(tv,sg.a,sg.cp1,sg.cp2,sg.b);
        const tv2=Math.min(tv+0.006,1),pt2=bez3(tv2,sg.a,sg.cp1,sg.cp2,sg.b);
        return{px:pt.x,py:pt.y,ang:Math.atan2(pt2.y-pt.y,pt2.x-pt.x)};
      }
      cum+=sg.len;
    }
    return null;
  }

  function frame(){
    if(!S.trackActive||S.trackPaused)return;
    const speed=S.trackSpeed*S.trackSpeedMult;
    S.trackT=Math.min(S.trackT+speed,1);
    S.wheelAngle+=speed*80;
    draw(S.bfsPath,S.dijkPath,hasB?S.trackT:null,hasD?S.trackT:null);
    cameraFollowVehicle(resolvePos(hasB?S.bfsPath:S.dijkPath,S.trackT));
    updateMinimap(S.bfsPath,S.dijkPath);
    if(S.trackT<1){S.raf=requestAnimationFrame(frame);}
    else{S.trackActive=false;btn.textContent='▶ Ulangi';btn.className='hbtn grn';notify('🏁 Sampai tujuan!');}
  }
  S.raf=requestAnimationFrame(frame);
}

function pauseTrack(){S.trackPaused=true;document.getElementById('btnTrack').textContent='▶ Lanjutkan';document.getElementById('btnTrack').className='hbtn grn';notify('⏸ Dijeda');}
function resumeTrack(){S.trackPaused=false;document.getElementById('btnTrack').textContent='⏸ Pause';document.getElementById('btnTrack').className='hbtn act';startTrack();}
function stopTrack(){S.trackActive=false;S.trackPaused=false;if(S.raf)cancelAnimationFrame(S.raf);S.trackT=0;S.trailBFS=[];S.trailDijk=[];document.getElementById('btnTrack').textContent='▶ Start Track';document.getElementById('btnTrack').className='hbtn grn';}
function notify(msg){const box=document.getElementById('nbox');const el=document.createElement('div');el.className='notif';el.textContent=msg;box.appendChild(el);requestAnimationFrame(()=>el.classList.add('show'));setTimeout(()=>{el.classList.remove('show');setTimeout(()=>el.remove(),220);},2600);}
function clearRes(){['rBP','rDP'].forEach(id=>document.getElementById(id).textContent='–');['rBD','rBH','rBT','rDD','rDH','rDT'].forEach(id=>document.getElementById(id).textContent='–');const sb=document.getElementById('rSummary');if(sb)sb.style.display='none';}

function init(seed){
  const res=generateMap(seed);
  Object.assign(S,{nodes:res.nodes,edges:res.edges,adj:res.adj,cc:res.cc,
    nodeBuildings:res.nodeBuildings,nodeTrees:res.nodeTrees,lakes:res.lakes,
    bfsPath:[],dijkPath:[]});
  stopTrack();populateSel();clearRes();draw();
}

// ============================================================
// EVENT LISTENERS (tidak berubah)
// ============================================================
document.getElementById('btnZI').onclick=()=>zoomTo(S.zoom*1.3);
document.getElementById('btnZO').onclick=()=>zoomTo(S.zoom/1.3);
document.getElementById('btnZR').onclick=()=>{
  const vp=document.getElementById('vp');
  const fz=Math.min(vp.clientWidth/MAP_W,vp.clientHeight/MAP_H)*0.94;
  S.zoom=fz;S.px=(vp.clientWidth-MAP_W*fz)/2;S.py=(vp.clientHeight-MAP_H*fz)/2;applyXform();
};
const vpEl=document.getElementById('vp');
vpEl.addEventListener('wheel',e=>{e.preventDefault();const r=e.currentTarget.getBoundingClientRect();zoomTo(S.zoom*(e.deltaY<0?1.13:0.88),e.clientX-r.left,e.clientY-r.top);},{passive:false});
vpEl.addEventListener('mousedown',e=>{S.drag=true;S.dsx=e.clientX;S.dsy=e.clientY;S.dpx=S.px;S.dpy=S.py;vpEl.classList.add('drag');});
window.addEventListener('mousemove',e=>{if(!S.drag)return;S.px=S.dpx+(e.clientX-S.dsx);S.py=S.dpy+(e.clientY-S.dsy);clampPan();applyXform();});
window.addEventListener('mouseup',()=>{S.drag=false;vpEl.classList.remove('drag');});
document.getElementById('btnRand').onclick=()=>{stopTrack();init(Math.floor(Math.random()*1e9));notify('🔀 Peta baru!');};
document.getElementById('btnRandPos').onclick=()=>{
  const n=S.nodes.length;
  // Coba semua pasangan secara acak sampai ketemu yang BFS ≠ Dijkstra
  const indices=[...Array(n).keys()];
  // Acak urutan supaya tidak selalu mulai dari node 0
  indices.sort(()=>Math.random()-0.5);
  let found=false;
  for(let a=0;a<indices.length&&!found;a++){
    for(let b=0;b<indices.length&&!found;b++){
      const s=indices[a],e=indices[b];
      if(s===e) continue;
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
  if(!found) notify('⚠️ Semua jalur sama di peta ini, coba Acak Map');
};
document.getElementById('btnTrack').onclick=()=>{
  if(!S.trackActive){S.trackT=0;S.trailBFS=[];S.trailDijk=[];startTrack();}
  else if(!S.trackPaused)pauseTrack();else resumeTrack();
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
  const mx=(e.clientX-r.left)/MM_W,my=(e.clientY-r.top)/MM_H;
  const vp=document.getElementById('vp');
  S.px=-(mx*MAP_W*S.zoom-vp.clientWidth/2);
  S.py=-(my*MAP_H*S.zoom-vp.clientHeight/2);
  clampPan();applyXform();
});

window.addEventListener('load',()=>{
  const vp=document.getElementById('vp');
  const fz=Math.min(vp.clientWidth/MAP_W,vp.clientHeight/MAP_H)*0.92;
  S.zoom=fz;S.px=(vp.clientWidth-MAP_W*fz)/2;S.py=(vp.clientHeight-MAP_H*fz)/2;
  init();applyXform();
  notify('🗺️ Peta siap! Jarak dalam km · BFS=min hop, Dijkstra=min km');
});