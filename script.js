/* ============================================================
   SCHED//SIM — CPU Scheduling Simulator
   ============================================================ */

/* ---------- palette for process chips ---------- */
const PALETTE = [
  {bg:'#5eead4', text:'#04140f'}, // cyan
  {bg:'#fbbf24', text:'#04140f'}, // amber
  {bg:'#f472b6', text:'#04140f'}, // magenta
  {bg:'#a78bfa', text:'#04140f'}, // violet
  {bg:'#7dd3fc', text:'#04140f'}, // sky
  {bg:'#fb923c', text:'#04140f'}, // orange
  {bg:'#86efac', text:'#04140f'}, // green
  {bg:'#fca5a5', text:'#04140f'}, // rose
];
function colorFor(idx){ return PALETTE[idx % PALETTE.length]; }

/* ---------- app state ---------- */
let processes = [];      // {id, label, arrival, burst, priority, colorIdx}
let nextPid = 1;
let currentAlgo = 'fcfs';
let currentMode = 'non'; // 'non' | 'pre'
let quantum = 2;

let simTicks = [];       // per-tick snapshots from the engine
let simGantt = [];       // merged gantt blocks
let simMetrics = null;
let playState = { playing:false, idx:0, timer:null };

/* ============================================================
   ALGORITHM METADATA
   ============================================================ */
const ALGO_INFO = {
  fcfs: {
    name:'First Come, First Served',
    modes:['non'],
    desc:'Processes are executed strictly in the order they arrive. Simple and fair by the clock, but a single long process at the front makes everyone behind it wait — the "convoy effect".',
    card:{
      pros:['Simple to implement','No starvation — everyone eventually runs'],
      cons:['Convoy effect: short jobs stuck behind long ones','Poor average waiting time'],
    }
  },
  sjf: {
    name:'Shortest Job First',
    modes:['non','pre'],
    desc:'Always picks the process with the smallest burst time. Non‑preemptive waits for the CPU to free up; the preemptive version (Shortest Remaining Time First) can interrupt a running process the instant a shorter one arrives.',
    card:{
      pros:['Optimal average waiting time (provably minimal)','Preemptive version reacts instantly to shorter arrivals'],
      cons:['Needs to know burst time in advance','Long processes can starve under heavy load'],
    }
  },
  rr: {
    name:'Round Robin',
    modes:['pre'],
    desc:'Every process gets a fixed time quantum on the CPU, then is sent to the back of the ready queue. Great for responsiveness in time‑sharing systems — the smaller the quantum, the more it behaves like fair sharing (at the cost of overhead).',
    card:{
      pros:['Fair, predictable response time','No starvation — everyone gets a turn'],
      cons:['Average waiting time worsens if quantum is badly tuned','Overhead from frequent context switches'],
    }
  },
  priority: {
    name:'Priority Scheduling',
    modes:['non','pre'],
    desc:'Each process carries a priority number (lower = runs first here). The CPU always goes to the highest‑priority ready process. Preemptive priority can interrupt a running process the moment something more important arrives.',
    card:{
      pros:['Important tasks get served first','Flexible — priority can model real urgency'],
      cons:['Low‑priority processes can starve indefinitely','Needs aging to guarantee fairness'],
    }
  }
};

/* ============================================================
   SCHEDULING ENGINE — tick based simulation
   returns { ticks:[{t, notArrived:[], ready:[], running:id|null, done:[]}],
             gantt:[{pid,start,end}],
             perProcess:{id:{completion,waiting,turnaround}} }
   ============================================================ */
function runScheduler(procs, algo, mode, q){
  const P = procs.map(p => ({...p, remaining:p.burst}));
  const byId = Object.fromEntries(P.map(p=>[p.id,p]));
  const n = P.length;
  if(n===0) return {ticks:[], gantt:[], perProcess:{}};

  let t = 0;
  let ready = [];           // array of ids, order = queue order
  let running = null;
  let rrTimer = 0;
  const completedAt = {};
  const startedAt = {};
  const notYetArrived = () => P.filter(p => p.arrival > t).map(p=>p.id);
  const doneIds = () => Object.keys(completedAt).map(Number);
  const ticks = [];
  const rawEvents = []; // {t, pid|null}

  const arrivedSet = new Set();

  function addArrivals(){
    P.forEach(p=>{
      if(p.arrival === t && !arrivedSet.has(p.id)){
        arrivedSet.add(p.id);
        ready.push(p.id);
      }
    });
  }

  function pickBy(comparatorPool, keyFn){
    // returns id with min keyFn, tie-break by arrival then id
    let best = null;
    comparatorPool.forEach(id=>{
      const p = byId[id];
      if(best===null) { best = id; return; }
      const bp = byId[best];
      const kv = keyFn(p), bv = keyFn(bp);
      if(kv < bv || (kv===bv && (p.arrival<bp.arrival || (p.arrival===bp.arrival && p.id<bp.id)))){
        best = id;
      }
    });
    return best;
  }

  const maxIter = 100000;
  let iter = 0;
  const totalBurst = P.reduce((s,p)=>s+p.burst,0);
  const lastArrival = Math.max(...P.map(p=>p.arrival));
  const safetyLimit = totalBurst + lastArrival + 5;

  while(doneIds().length < n && iter < maxIter && t <= safetyLimit){
    iter++;
    addArrivals();

    if(algo==='fcfs'){
      if(running===null && ready.length){
        running = ready.shift();
        startedAt[running] = startedAt[running] ?? t;
      }
    }
    else if(algo==='sjf' && mode==='non'){
      if(running===null && ready.length){
        const pick = pickBy(ready, p=>p.remaining);
        ready = ready.filter(id=>id!==pick);
        running = pick;
        startedAt[running] = startedAt[running] ?? t;
      }
    }
    else if(algo==='sjf' && mode==='pre'){
      const pool = running!==null ? [...ready, running] : [...ready];
      if(pool.length){
        const pick = pickBy(pool, p=>p.remaining);
        if(pick !== running){
          if(running!==null) ready.push(running);
          ready = ready.filter(id=>id!==pick);
          running = pick;
          startedAt[running] = startedAt[running] ?? t;
          rrTimer = 0;
        }
      }
    }
    else if(algo==='priority' && mode==='non'){
      if(running===null && ready.length){
        const pick = pickBy(ready, p=>p.priority);
        ready = ready.filter(id=>id!==pick);
        running = pick;
        startedAt[running] = startedAt[running] ?? t;
      }
    }
    else if(algo==='priority' && mode==='pre'){
      const pool = running!==null ? [...ready, running] : [...ready];
      if(pool.length){
        const pick = pickBy(pool, p=>p.priority);
        if(pick !== running){
          if(running!==null) ready.push(running);
          ready = ready.filter(id=>id!==pick);
          running = pick;
          startedAt[running] = startedAt[running] ?? t;
          rrTimer = 0;
        }
      }
    }
    else if(algo==='rr'){
      if(running===null && ready.length){
        running = ready.shift();
        startedAt[running] = startedAt[running] ?? t;
        rrTimer = 0;
      }
    }

    // record snapshot BEFORE executing this tick's unit of work
    ticks.push({
      t,
      notArrived: notYetArrived(),
      ready: [...ready],
      running,
      done: doneIds()
    });
    rawEvents.push({t, pid: running});

    if(running!==null){
      byId[running].remaining -= 1;
      if(algo==='rr') rrTimer += 1;

      if(byId[running].remaining === 0){
        completedAt[running] = t+1;
        running = null;
        rrTimer = 0;
      } else if(algo==='rr' && rrTimer===q){
        // quantum expired -> requeue at back (after arrivals already added at loop start for t+1 handled next loop)
        ready.push(running);
        running = null;
        rrTimer = 0;
      }
    }

    t += 1;
  }

  // final snapshot (all done)
  ticks.push({ t, notArrived: notYetArrived(), ready:[...ready], running:null, done: doneIds() });

  // build gantt blocks from rawEvents (merge consecutive same pid, incl idle as null)
  const gantt = [];
  rawEvents.forEach(ev=>{
    const last = gantt[gantt.length-1];
    if(last && last.pid === ev.pid){ last.end = ev.t+1; }
    else gantt.push({pid: ev.pid, start: ev.t, end: ev.t+1});
  });

  const perProcess = {};
  P.forEach(p=>{
    const completion = completedAt[p.id];
    const turnaround = completion - p.arrival;
    const waiting = turnaround - p.burst;
    perProcess[p.id] = { completion, turnaround, waiting, arrival:p.arrival, burst:p.burst };
  });

  return { ticks, gantt, perProcess };
}

/* ============================================================
   DOM refs
   ============================================================ */
const $ = sel => document.querySelector(sel);
const algoTabs = $('#algoTabs');
const modeGroup = $('#modeGroup');
const modeToggle = $('#modeToggle');
const quantumGroup = $('#quantumGroup');
const quantumInput = $('#quantumInput');
const algoDesc = $('#algoDesc');

const processForm = $('#processForm');
const pidDisplay = $('#pidDisplay');
const arrivalInput = $('#arrivalInput');
const burstInput = $('#burstInput');
const priorityInput = $('#priorityInput');
const priorityField = $('#priorityField');
const priorityHeader = $('#priorityHeader');
const processTableBody = $('#processTableBody');
const emptyHint = $('#emptyHint');
const runBtn = $('#runBtn');
const compareBtn = $('#compareBtn');
const sampleBtn = $('#sampleBtn');
const clearBtn = $('#clearBtn');

const notArrivedLane = $('#notArrivedLane');
const readyLane = $('#readyLane');
const doneLane = $('#doneLane');
const cpuBox = $('#cpuBox');
const cpuEmptyText = $('#cpuEmptyText');
const tickReadout = $('#tickReadout');
const clockValue = $('#clockValue');
const ganttTrack = $('#ganttTrack');
const ganttRuler = $('#ganttRuler');
const metricsWrap = $('#metricsWrap');
const metricsBody = $('#metricsBody');
const metricsSummary = $('#metricsSummary');

const playPauseBtn = $('#playPauseBtn');
const playIcon = $('#playIcon');
const pauseIcon = $('#pauseIcon');
const stepBtn = $('#stepBtn');
const restartBtn = $('#restartBtn');
const speedRange = $('#speedRange');

/* ============================================================
   ALGO TAB / MODE / QUANTUM UI
   ============================================================ */
algoTabs.addEventListener('click', e=>{
  const btn = e.target.closest('.algo-tab');
  if(!btn) return;
  currentAlgo = btn.dataset.algo;
  [...algoTabs.children].forEach(b=>b.classList.toggle('active', b===btn));
  updateAlgoOptionsUI();
  renderProcessTable();
});

modeToggle.addEventListener('click', e=>{
  const btn = e.target.closest('.toggle-btn');
  if(!btn) return;
  currentMode = btn.dataset.mode;
  [...modeToggle.children].forEach(b=>b.classList.toggle('active', b===btn));
});

$('#qMinus').addEventListener('click', ()=>{ quantum = Math.max(1, quantum-1); quantumInput.value = quantum; });
$('#qPlus').addEventListener('click', ()=>{ quantum = Math.min(20, quantum+1); quantumInput.value = quantum; });
quantumInput.addEventListener('change', ()=>{ quantum = Math.max(1, Math.min(20, Number(quantumInput.value)||2)); quantumInput.value = quantum; });

function updateAlgoOptionsUI(){
  const info = ALGO_INFO[currentAlgo];
  algoDesc.textContent = info.desc;

  // mode toggle visibility
  if(info.modes.length > 1){
    modeGroup.style.display = 'flex';
    if(!info.modes.includes(currentMode)) currentMode = info.modes[0];
    [...modeToggle.children].forEach(b=> b.classList.toggle('active', b.dataset.mode===currentMode));
  } else {
    currentMode = info.modes[0];
    modeGroup.style.display = 'none';
  }

  quantumGroup.style.display = (currentAlgo==='rr') ? 'flex' : 'none';
  priorityField.style.display = (currentAlgo==='priority') ? 'flex' : 'none';
  priorityHeader.style.display = (currentAlgo==='priority') ? '' : 'none';
  [...processTableBody.children].forEach(tr=>{
    const cell = tr.querySelector('.priority-cell');
    if(cell) cell.style.display = (currentAlgo==='priority') ? '' : 'none';
  });
}

/* set initial active tab */
[...algoTabs.children].forEach(b=> b.classList.toggle('active', b.dataset.algo===currentAlgo));
updateAlgoOptionsUI();

/* ============================================================
   PROCESS FORM / TABLE
   ============================================================ */
pidDisplay.textContent = 'P'+nextPid;

processForm.addEventListener('submit', e=>{
  e.preventDefault();
  const arrival = Math.max(0, Number(arrivalInput.value)||0);
  const burst = Math.max(1, Number(burstInput.value)||1);
  const priority = Math.max(1, Number(priorityInput.value)||1);
  const colorIdx = processes.length;
  const p = { id: nextPid, label:'P'+nextPid, arrival, burst, priority, colorIdx };
  processes.push(p);
  nextPid += 1;
  pidDisplay.textContent = 'P'+nextPid;
  arrivalInput.value = arrival; // keep last for convenience
  burstInput.value = 5;
  priorityInput.value = 1;
  renderProcessTable();
  resetSimUI();
});

function renderProcessTable(){
  processTableBody.innerHTML = '';
  emptyHint.style.display = processes.length ? 'none' : 'block';
  processes.forEach(p=>{
    const c = colorFor(p.colorIdx);
    const tr = document.createElement('tr');
    tr.innerHTML = `
      <td><div class="pid-cell"><span class="pid-swatch" style="background:${c.bg}"></span>${p.label}</div></td>
      <td>${p.arrival}</td>
      <td>${p.burst}</td>
      <td class="priority-cell" style="display:${currentAlgo==='priority'?'':'none'}">${p.priority}</td>
      <td><button class="row-del" data-id="${p.id}" title="Remove">&times;</button></td>
    `;
    processTableBody.appendChild(tr);
  });
  runBtn.disabled = processes.length===0;
  compareBtn.disabled = processes.length===0;
}

processTableBody.addEventListener('click', e=>{
  const btn = e.target.closest('.row-del');
  if(!btn) return;
  const id = Number(btn.dataset.id);
  processes = processes.filter(p=>p.id!==id);
  renderProcessTable();
  resetSimUI();
});

sampleBtn.addEventListener('click', ()=>{
  processes = [];
  nextPid = 1;
  const sample = [
    {arrival:0, burst:6, priority:2},
    {arrival:1, burst:3, priority:1},
    {arrival:2, burst:8, priority:4},
    {arrival:3, burst:4, priority:3},
    {arrival:5, burst:2, priority:5},
  ];
  sample.forEach((s,i)=>{
    processes.push({ id:nextPid, label:'P'+nextPid, arrival:s.arrival, burst:s.burst, priority:s.priority, colorIdx:i });
    nextPid+=1;
  });
  pidDisplay.textContent = 'P'+nextPid;
  renderProcessTable();
  resetSimUI();
});

clearBtn.addEventListener('click', ()=>{
  processes = [];
  nextPid = 1;
  pidDisplay.textContent = 'P'+nextPid;
  renderProcessTable();
  resetSimUI();
});

/* ============================================================
   SIMULATION PLAYBACK
   ============================================================ */
function resetSimUI(){
  stopPlayback();
  simTicks = []; simGantt = []; simMetrics = null;
  notArrivedLane.innerHTML = ''; readyLane.innerHTML = ''; doneLane.innerHTML = '';
  cpuBox.classList.remove('busy');
  cpuBox.querySelectorAll('.cpu-running-chip').forEach(n=>n.remove());
  cpuEmptyText.style.display = 'block';
  tickReadout.textContent = 't = 0';
  clockValue.textContent = 't = 0';
  ganttTrack.innerHTML = ''; ganttRuler.innerHTML = '';
  metricsWrap.style.display = 'none';
}

runBtn.addEventListener('click', ()=>{
  if(processes.length===0) return;
  const result = runScheduler(processes, currentAlgo, currentMode, quantum);
  simTicks = result.ticks;
  simGantt = result.gantt;
  simMetrics = result.perProcess;
  playState = { playing:false, idx:0, timer:null };
  resetSimUI_keepData();
  $('#simPanel').scrollIntoView({behavior:'smooth', block:'start'});
  renderTick(0);
  startPlayback();
});

function resetSimUI_keepData(){
  notArrivedLane.innerHTML = ''; readyLane.innerHTML = ''; doneLane.innerHTML = '';
  ganttTrack.innerHTML = ''; ganttRuler.innerHTML = '';
  metricsWrap.style.display = 'none';
}

function speedMs(){
  const v = Number(speedRange.value);
  return {1:1000, 2:600, 3:350, 4:150}[v] || 600;
}

function startPlayback(){
  stopPlaybackTimerOnly();
  playState.playing = true;
  playIcon.style.display='none'; pauseIcon.style.display='block';
  playState.timer = setInterval(()=>{
    if(playState.idx >= simTicks.length-1){
      stopPlayback();
      showMetrics();
      return;
    }
    playState.idx += 1;
    renderTick(playState.idx);
  }, speedMs());
}
function stopPlaybackTimerOnly(){
  if(playState.timer) clearInterval(playState.timer);
  playState.timer = null;
}
function stopPlayback(){
  stopPlaybackTimerOnly();
  playState.playing = false;
  playIcon.style.display='block'; pauseIcon.style.display='none';
}

playPauseBtn.addEventListener('click', ()=>{
  if(!simTicks.length) return;
  if(playState.playing){ stopPlayback(); }
  else{
    if(playState.idx >= simTicks.length-1){ playState.idx = 0; }
    startPlayback();
  }
});
stepBtn.addEventListener('click', ()=>{
  if(!simTicks.length) return;
  stopPlayback();
  if(playState.idx < simTicks.length-1){
    playState.idx += 1;
    renderTick(playState.idx);
    if(playState.idx === simTicks.length-1) showMetrics();
  }
});
restartBtn.addEventListener('click', ()=>{
  if(!simTicks.length) return;
  stopPlayback();
  playState.idx = 0;
  resetSimUI_keepData();
  renderTick(0);
});
speedRange.addEventListener('input', ()=>{
  if(playState.playing){ startPlayback(); }
});

function chipHtml(p, extraClass=''){
  const c = colorFor(p.colorIdx);
  return `<div class="proc-chip ${extraClass}" style="background:${c.bg};color:${c.text};border-color:${c.bg}">
    <span>${p.label}</span><span class="chip-sub">rem ${p.remaining ?? p.burst}</span>
  </div>`;
}

function renderTick(idx){
  const snap = simTicks[idx];
  if(!snap) return;
  tickReadout.textContent = 't = ' + snap.t;
  clockValue.textContent = 't = ' + snap.t;

  const byId = Object.fromEntries(processes.map(p=>[p.id,p]));

  // remaining burst at this point in time (approx via re-derive from perProcess start not tracked per tick; recompute quickly)
  // We recompute remaining bursts by replaying ticks up to idx for display purposes.
  const remainingMap = computeRemainingAt(idx);

  notArrivedLane.innerHTML = snap.notArrived.map(id=>{
    const p = byId[id];
    return chipHtml({...p, remaining:p.burst}, 'dim');
  }).join('') || '<span class="empty-hint" style="padding:8px;">—</span>';

  readyLane.innerHTML = snap.ready.map(id=>{
    const p = byId[id];
    return chipHtml({...p, remaining:remainingMap[id]});
  }).join('') || '<span class="empty-hint" style="padding:8px;">—</span>';

  doneLane.innerHTML = snap.done.map(id=>{
    const p = byId[id];
    return chipHtml({...p, remaining:0});
  }).join('') || '<span class="empty-hint" style="padding:8px;">—</span>';

  cpuBox.querySelectorAll('.cpu-running-chip').forEach(n=>n.remove());
  if(snap.running !== null){
    cpuBox.classList.add('busy');
    cpuEmptyText.style.display = 'none';
    const p = byId[snap.running];
    const c = colorFor(p.colorIdx);
    const el = document.createElement('div');
    el.className = 'cpu-running-chip';
    el.style.color = c.bg;
    el.innerHTML = `<span>${p.label}</span><span class="chip-sub">rem ${remainingMap[snap.running]}</span>`;
    cpuBox.appendChild(el);
  } else {
    cpuBox.classList.remove('busy');
    cpuEmptyText.style.display = 'block';
  }

  renderGanttUpTo(snap.t);
}

function computeRemainingAt(idx){
  const remaining = {};
  processes.forEach(p=> remaining[p.id] = p.burst);
  for(let i=0;i<idx;i++){
    const running = simTicks[i].running;
    if(running!==null) remaining[running] -= 1;
  }
  return remaining;
}

function renderGanttUpTo(t){
  const blocksToShow = simGantt.filter(b=>b.start < t || (b.start===0 && t===0 && b.start<=t));
  const visible = simGantt.filter(b => b.start < t);
  // include the in-progress block partially
  ganttTrack.innerHTML = '';
  ganttRuler.innerHTML = '';
  const byId = Object.fromEntries(processes.map(p=>[p.id,p]));
  const totalSpan = Math.max(t, 1);

  let cursor = 0;
  simGantt.forEach(b=>{
    if(b.start >= t) return;
    const end = Math.min(b.end, t);
    const width = end - b.start;
    if(width<=0) return;
    const div = document.createElement('div');
    div.className = 'gantt-block' + (b.pid===null ? ' idle' : '');
    const pct = (width/totalSpanFull())*100;
    div.style.width = pct + '%';
    if(b.pid!==null){
      const c = colorFor(byId[b.pid].colorIdx);
      div.style.background = c.bg; div.style.color = c.text;
      div.textContent = byId[b.pid].label;
    } else {
      div.textContent = '';
    }
    ganttTrack.appendChild(div);
    cursor = end;
  });

  // ruler marks every block boundary up to t
  const marks = new Set([0]);
  simGantt.forEach(b=>{ if(b.start<=t) marks.add(b.start); if(b.end<=t) marks.add(b.end); });
  marks.add(t);
  const sorted = [...marks].sort((a,b)=>a-b);
  for(let i=0;i<sorted.length-1;i++){
    const w = sorted[i+1]-sorted[i];
    if(w<=0) continue;
    const span = document.createElement('div');
    span.className='gantt-tick';
    span.style.width = (w/totalSpanFull()*100)+'%';
    span.textContent = sorted[i];
    ganttRuler.appendChild(span);
  }
  const lastSpan = document.createElement('div');
  lastSpan.className='gantt-tick';
  lastSpan.style.width='0';
  lastSpan.textContent = t;
  ganttRuler.appendChild(lastSpan);
}
function totalSpanFull(){
  if(!simGantt.length) return 1;
  return Math.max(...simGantt.map(b=>b.end), 1);
}

function showMetrics(){
  metricsWrap.style.display = 'block';
  metricsBody.innerHTML = '';
  const byId = Object.fromEntries(processes.map(p=>[p.id,p]));
  let totalWait=0, totalTurn=0, n=0;
  processes.forEach(p=>{
    const m = simMetrics[p.id];
    if(!m) return;
    n++; totalWait+=m.waiting; totalTurn+=m.turnaround;
    const c = colorFor(p.colorIdx);
    const tr = document.createElement('tr');
    tr.innerHTML = `<td><span class="pid-swatch" style="background:${c.bg};display:inline-block;margin-right:6px;border-radius:2px;width:9px;height:9px;"></span>${p.label}</td>
      <td>${m.arrival}</td><td>${m.burst}</td><td>${m.completion}</td><td>${m.turnaround}</td><td>${m.waiting}</td>`;
    metricsBody.appendChild(tr);
  });
  const avgWait = (totalWait/n).toFixed(2);
  const avgTurn = (totalTurn/n).toFixed(2);
  metricsSummary.innerHTML = `
    <div class="summary-card"><div class="label">AVG WAITING TIME</div><div class="value">${avgWait}</div></div>
    <div class="summary-card"><div class="label">AVG TURNAROUND TIME</div><div class="value">${avgTurn}</div></div>
    <div class="summary-card"><div class="label">TOTAL PROCESSES</div><div class="value">${n}</div></div>
  `;
}

/* ============================================================
   ALGORITHM INFO CARDS
   ============================================================ */
function renderInfoGrid(){
  const grid = $('#infoGrid');
  grid.innerHTML = '';
  Object.entries(ALGO_INFO).forEach(([key, info])=>{
    const card = document.createElement('div');
    card.className = 'info-card' + (key===currentAlgo ? ' highlighted' : '');
    card.innerHTML = `
      <h3>${info.name}</h3>
      <p>${info.desc}</p>
      <div class="info-tags">
        ${info.card.pros.map(x=>`<span class="info-tag good">+ ${x}</span>`).join('')}
        ${info.card.cons.map(x=>`<span class="info-tag bad">- ${x}</span>`).join('')}
      </div>
    `;
    grid.appendChild(card);
  });
}
renderInfoGrid();
const _origUpdateAlgoOptionsUI = updateAlgoOptionsUI;
algoTabs.addEventListener('click', ()=> renderInfoGrid());

/* ============================================================
   COMPARISON MODE
   ============================================================ */
compareBtn.addEventListener('click', ()=>{
  if(processes.length===0) return;
  const sjfMode = currentAlgo==='sjf' ? currentMode : 'non';
  const prMode = currentAlgo==='priority' ? currentMode : 'non';
  const configs = [
    {key:'fcfs', label:'FCFS', algo:'fcfs', mode:'non'},
    {key:'sjf', label:'SJF ('+(sjfMode==='pre'?'preemptive':'non-preemptive')+')', algo:'sjf', mode: sjfMode},
    {key:'rr', label:'Round Robin (q='+quantum+')', algo:'rr', mode:'pre'},
    {key:'priority', label:'Priority ('+(prMode==='pre'?'preemptive':'non-preemptive')+')', algo:'priority', mode: prMode},
  ];

  const results = configs.map(cfg=>{
    const r = runScheduler(processes, cfg.algo, cfg.mode, quantum);
    let totalWait=0, totalTurn=0, n=0, switches=0;
    processes.forEach(p=>{
      const m = r.perProcess[p.id];
      if(!m) return;
      n++; totalWait+=m.waiting; totalTurn+=m.turnaround;
    });
    let lastPid = undefined;
    r.gantt.forEach(b=>{ if(b.pid!==null){ if(lastPid!==undefined && lastPid!==b.pid) switches++; lastPid=b.pid; } });
    return { ...cfg, avgWait: totalWait/n, avgTurn: totalTurn/n, switches };
  });

  const maxWait = Math.max(...results.map(r=>r.avgWait), 1);
  const chart = $('#compareChart');
  chart.innerHTML = results.map(r=>{
    const pct = (r.avgWait/maxWait*100).toFixed(1);
    return `<div class="compare-row">
      <div class="compare-row-label">${r.label}</div>
      <div class="compare-bar-track"><div class="compare-bar-fill" style="background:${barColor(r.key)}"><span>${r.avgWait.toFixed(2)}</span></div></div>
    </div>`;
  }).join('');
  // animate widths after paint
  requestAnimationFrame(()=>{
    requestAnimationFrame(()=>{
      [...chart.querySelectorAll('.compare-bar-fill')].forEach((el,i)=>{
        el.style.width = (results[i].avgWait/maxWait*100)+'%';
      });
    });
  });

  const winner = results.reduce((a,b)=> b.avgWait < a.avgWait ? b : a);
  $('#winnerBanner').innerHTML = `For this exact process set, <b>${winner.label}</b> gives the lowest average waiting time — <b>${winner.avgWait.toFixed(2)}</b> — beating the others by an average of ${(results.reduce((s,r)=>s+r.avgWait,0)/results.length - winner.avgWait).toFixed(2)} time units.`;

  const body = $('#compareBody');
  body.innerHTML = results.map(r=>`
    <tr ${r.key===winner.key?'style="color:#5eead4;font-weight:700;"':''}>
      <td>${r.label}${r.key===winner.key?' 🏆':''}</td>
      <td>${r.avgWait.toFixed(2)}</td>
      <td>${r.avgTurn.toFixed(2)}</td>
      <td>${r.switches}</td>
    </tr>
  `).join('');

  $('#compareResults').style.display = 'block';
  $('#compareResults').scrollIntoView({behavior:'smooth', block:'start'});
});

function barColor(key){
  return { fcfs:'#5eead4', sjf:'#fbbf24', rr:'#f472b6', priority:'#a78bfa' }[key] || '#5eead4';
}

/* ============================================================
   HERO SCROLL CUE
   ============================================================ */
$('#scrollCue').addEventListener('click', ()=>{
  $('#appSection').scrollIntoView({behavior:'smooth', block:'start'});
});

/* init */
renderProcessTable();
