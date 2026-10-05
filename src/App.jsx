import React, { useState, useEffect, useRef, createContext, useContext } from "react";
import {
  LayoutDashboard, FlaskConical, Network, Wand2, ArrowDownUp, ListOrdered, Compass, Trophy, Boxes,
  GraduationCap, Info, Play, Pause, SkipBack, SkipForward, Sun, Moon, Menu, X, Plus, Trash2, Shuffle,
  Check, AlertTriangle, Code2, ShieldCheck, Hammer, GitCompare, Copy, RotateCcw, Sparkles, ChevronRight,
  Activity, Flag, Eye,
} from "lucide-react";
import { LineChart, Line, XAxis, YAxis, Tooltip as RTooltip, CartesianGrid, Legend as RLegend, ResponsiveContainer } from "recharts";

/* ==LOGIC-START== */
let _id = 1;
const uid = () => _id++;
const mk = (vals) => vals.map((v) => ({ id: uid(), v }));
// a has strictly higher priority than b (ties broken by arrival time t)
const lt = (type, a, b) => {
  if (a.v !== b.v) return type === "min" ? a.v < b.v : a.v > b.v;
  return (a.t ?? 0) < (b.t ?? 0);
};
const levelsOf = (n) => (n ? Math.floor(Math.log2(n)) + 1 : 0);
const depthOf = (i) => Math.floor(Math.log2(i + 1));
const parentOf = (i) => (i - 1) >> 1;
const rel = (a, b) => (a < b ? "<" : a > b ? ">" : "=");
const fmt = (v) => {
  const a = Math.abs(v);
  if (a >= 1e6) return v.toExponential(1).replace("+", "");
  if (Number.isInteger(v)) return String(v);
  return String(Number(v.toFixed(1)));
};
function parseVals(s) {
  const toks = s.split(/[\s,;]+/).filter(Boolean);
  const vals = [], bad = [];
  toks.forEach((t) => {
    if (/^[-+]?(\d+\.?\d*|\.\d+)$/.test(t)) vals.push(Number(t));
    else bad.push(t);
  });
  return { vals, bad };
}
function validate(arr, type, size = arr.length) {
  const out = [];
  for (let i = 1; i < size; i++) {
    const p = parentOf(i);
    if (arr[i] && arr[p] && lt(type, arr[i], arr[p]))
      out.push({ p, c: i, msg: `Node ${arr[p].v} (index ${p}) ${type === "min" ? ">" : "<"} child ${arr[i].v} (index ${i}) — heap property violated at index ${p}.` });
  }
  return out;
}

function newRec(type, arr, extra = {}) {
  const R = { type, a: arr.slice(), size: arr.length, st: { c: 0, s: 0 }, ck: new Set(), steps: [], extra };
  R.push = (o) => {
    const m = o.marks || {};
    (m.cmp || []).forEach((x) => R.ck.add(x));
    R.steps.push({ ...o, marks: m, arr: R.a.slice(), size: R.size, cmps: R.st.c, swaps: R.st.s, checked: R.ck.size, ...R.extra });
  };
  return R;
}
const sw = (R, i, j) => { [R.a[i], R.a[j]] = [R.a[j], R.a[i]]; R.st.s++; };
const ln = (L, w) => (L.sub ? { line: L.call, sline: w, sub: L.sub } : { line: w });
const UP_INS = { sub: false, cmp: 3, swap: 4 };
const UP_SUB = (call) => ({ sub: "up", call, cmp: 1, swap: 2 });
const DOWN = (call) => ({ sub: call == null ? false : "down", call, l: 1, leaf: 2, r: 3, chk: 4, swap: 5 });
const fin = (R, title, m, o = {}) =>
  R.push({ marks: { root: R.size ? [0] : [] }, title, done: true, action: "Complete", violation: false, m, ...o });
const res = (R) => ({ steps: R.steps, arr: R.a, st: R.st });

function siftUp(R, i, L) {
  const T = R.type, sm = T === "min" ? "smaller" : "larger";
  while (i > 0) {
    const p = parentOf(i), c = R.a[i], pr = R.a[p];
    R.st.c++;
    const bad = lt(T, c, pr);
    R.push({
      marks: { cmp: [i, p] }, title: `Comparing ${c.v} with parent ${pr.v}`, cmp: `${fmt(c.v)} ${rel(c.v, pr.v)} ${fmt(pr.v)}`,
      action: bad ? "Swap required" : "No swap needed", violation: bad, ...ln(L, L.cmp),
      m: bad
        ? `${c.v} is ${sm} than its parent ${pr.v}, so the ${T}-heap property is violated. The algorithm swaps them and keeps climbing.`
        : `${c.v} is not ${sm} than its parent ${pr.v}, so the ${T}-heap property already holds here. Climbing stops.`,
    });
    if (!bad) break;
    sw(R, i, p);
    R.push({ marks: { swap: [p, i] }, title: `Swapped ${c.v} with ${pr.v}`, action: "Swapped", ...ln(L, L.swap), m: `${c.v} moved up to index ${p}. Next it is compared with its new parent.` });
    i = p;
  }
  return i;
}

function siftDown(R, i, size, L) {
  const T = R.type, sm = T === "min" ? "smaller" : "larger";
  let it = 0;
  while (true) {
    const l = 2 * i + 1, r = l + 1, v = R.a[i].v;
    if (l >= size) {
      R.push({ marks: { cur: [i] }, title: `${v} at index ${i} has no children (leaf)`, action: "Stop", ph: 6, ...ln(L, L.leaf), m: `${v} has no children inside the heap, so nothing below it can be violated. Heapify-down stops.` });
      break;
    }
    const kids = r < size ? [l, r] : [l];
    R.push({
      marks: { cur: [i], cmp: kids }, ph: it ? 5 : 1, ...ln(L, L.l), action: "Select subtree",
      title: kids.length === 2 ? `Examining ${v} with children ${R.a[l].v} and ${R.a[r].v}` : `Examining ${v} with its only child ${R.a[l].v}`,
      m: `Index ${i} has children at 2i+1 = ${l}${kids.length === 2 ? ` and 2i+2 = ${r}` : ""}. The ${sm} child is the only candidate that can safely move up.`,
    });
    it++;
    let kid = l;
    if (r < size) {
      R.st.c++;
      kid = lt(T, R.a[r], R.a[l]) ? r : l;
      R.push({
        marks: { cmp: [l, r] }, ph: 2, ...ln(L, L.r), title: `Comparing children ${R.a[l].v} and ${R.a[r].v}`, cmp: `${fmt(R.a[l].v)} ${rel(R.a[l].v, R.a[r].v)} ${fmt(R.a[r].v)}`,
        action: `Pick ${sm} child ${R.a[kid].v}`, kid, m: `${R.a[kid].v} is the ${sm} child, so it is the one compared with ${v}.`,
      });
    }
    R.st.c++;
    const bad = lt(T, R.a[kid], R.a[i]);
    R.push({
      marks: { cmp: [i, kid] }, ph: 3, ...ln(L, L.chk), title: `Comparing ${v} with ${sm} child ${R.a[kid].v}`, cmp: `${fmt(v)} ${rel(v, R.a[kid].v)} ${fmt(R.a[kid].v)}`,
      action: bad ? "Swap required" : "No swap needed", violation: bad, kid,
      m: bad ? `${R.a[kid].v} is ${sm} than ${v}, so the ${T}-heap property is violated. They swap and ${v} keeps sinking.` : `${v} is already ${sm} than or equal to its children, so it is in the right place.`,
    });
    if (!bad) break;
    sw(R, i, kid);
    R.push({ marks: { swap: [i, kid] }, ph: 4, ...ln(L, L.swap), title: `Swapped ${v} with ${R.a[i].v}`, action: "Swapped", kid, m: `${v} moved down to index ${kid}. The loop continues from there.` });
    i = kid;
  }
  return i;
}

function opInsert(arr, type, item) {
  const R = newRec(type, arr), T = type;
  R.push({ title: `Inserting ${item.v} into the ${T}-heap`, action: "Start", line: 0, m: `Insertion always writes at the end of the array, so the tree stays complete. Then ${item.v} is moved up until the ${T}-heap property holds.` });
  R.a.push(item); R.size = R.a.length;
  const i = R.a.length - 1;
  R.push({ marks: { new: [i] }, title: `Added ${item.v} at the end (index ${i})`, action: "Append", line: 1, m: `${item.v} is placed at index ${i}, the next free slot of the complete tree. The heap order may now be broken locally.` });
  const s0 = R.st.s;
  if (i > 0) {
    const p = parentOf(i);
    R.push({ marks: { new: [i], cur: [p] }, title: `Parent of index ${i} is index ${p} (value ${R.a[p].v})`, action: "Locate parent", line: 2, m: `Parent index = floor((${i} - 1) / 2) = ${p}.` });
    siftUp(R, i, UP_INS);
  }
  fin(R, "Heap property restored", `${item.v} is in place after ${R.st.s - s0} swap(s). The array is a valid ${T}-heap again.`);
  return res(R);
}

function opExtract(arr, type) {
  const R = newRec(type, arr), T = type, nm = T === "min" ? "minimum" : "maximum";
  const root = R.a[0];
  R.extra.out = root.v;
  R.push({ marks: { root: [0] }, title: `Root ${root.v} is the ${nm} — extracting it`, action: "Read root", line: 2, m: `In a ${T}-heap the ${nm} always sits at index 0, so extraction is just reading the root.` });
  R.push({ marks: { rem: [0] }, title: `Removing root ${root.v}`, action: "Remove", line: 3, m: `The root slot is now empty. To keep the tree complete, the last element is moved into it.` });
  if (R.a.length === 1) {
    R.a.pop(); R.size = 0;
    fin(R, `Heap is now empty (extracted ${root.v})`, `${root.v} was the only element.`);
    return res(R);
  }
  const last = R.a.pop(); R.a[0] = last; R.size--;
  R.push({ marks: { new: [0] }, title: `Moved last element ${last.v} to the root`, action: "Move last to root", line: 3, violation: validate(R.a, T).length > 0, m: `${last.v} now sits at the root, which probably breaks the ${T}-heap property. Heapify-down will repair it.` });
  siftDown(R, 0, R.size, DOWN(4));
  fin(R, `Heap restored — extracted ${root.v}`, `${root.v} was returned and the remaining ${R.size} elements form a valid ${T}-heap.`);
  return res(R);
}

function opDeleteAt(arr, type, idx) {
  const R = newRec(type, arr), T = type, it = R.a[idx];
  R.extra.out = it.v;
  R.push({ marks: { rem: [idx] }, title: `Deleting ${it.v} at index ${idx}`, action: "Remove", line: 0, m: `Deleting replaces the node with the last element of the array, then repairs the heap in whichever direction is needed.` });
  const last = R.a.pop(); R.size--;
  if (idx === R.a.length) {
    fin(R, `Removed the last element ${it.v}`, `${it.v} was the last array element, so nothing needs repairing.`, { line: 1 });
    return res(R);
  }
  R.a[idx] = last;
  R.push({ marks: { new: [idx] }, title: `Moved last element ${last.v} into index ${idx}`, action: "Fill the gap", line: 1, violation: validate(R.a, T).length > 0, m: `${last.v} fills the gap. It may need to move up or down.` });
  const up = idx > 0 && lt(T, R.a[idx], R.a[parentOf(idx)]);
  R.push({ marks: { cmp: idx > 0 ? [idx, parentOf(idx)] : [idx] }, title: up ? `${last.v} beats its parent — sift up` : `Sift ${last.v} down from index ${idx}`, action: up ? "Heapify up" : "Heapify down", line: 2, m: up ? `${last.v} has higher priority than its new parent, so it climbs.` : `${last.v} does not beat its parent, so any violation can only be below it.` });
  if (up) siftUp(R, idx, UP_SUB(3)); else siftDown(R, idx, R.size, DOWN(5));
  fin(R, `Heap restored after deleting ${it.v}`, `Deleted ${it.v}; the remaining elements form a valid ${T}-heap.`);
  return res(R);
}

function opBuild(arr, type) {
  const R = newRec(type, arr), n = R.a.length;
  R.push({ title: `Starting from the array as given (${n} elements)`, action: "Start", line: 0, m: `Build-heap does not insert one by one. It starts at the last non-leaf node, index floor(n/2) - 1 = ${(n >> 1) - 1}, and heapifies each node down to the root.` });
  for (let i = (n >> 1) - 1; i >= 0; i--) {
    R.extra.cur = i;
    R.push({ marks: { cur: [i] }, title: `Heapify at index ${i} (value ${R.a[i].v})`, action: "Next node", line: 1, m: `Index ${i} is the next non-leaf node, moving from the last one toward the root. Both of its subtrees are already heaps, so one heapify-down is enough.` });
    siftDown(R, i, n, DOWN(2));
  }
  R.extra.cur = null;
  fin(R, "Build complete — heap restored", `Every non-leaf node was heapified, so the whole array is a valid ${type}-heap. Total cost is O(n), not O(n log n).`);
  return res(R);
}

function opHeapifyAt(arr, type, i) {
  const R = newRec(type, arr);
  R.push({ marks: { cur: [i] }, title: `Heapify-down at index ${i} (value ${R.a[i].v})`, action: "Start", ph: 0, line: 0, m: `Heapify assumes the subtrees below index ${i} are already heaps. It only fixes the single node ${R.a[i].v} by sinking it.` });
  siftDown(R, i, R.size, DOWN(null));
  fin(R, "Subtree is a heap again", `The node sank until both children were no better than it.`);
  return res(R);
}

function opSort(arr, dir) {
  const T = dir === "asc" ? "max" : "min", n = arr.length;
  const R = newRec(T, arr, { sortedFrom: n, phase: "Building heap", iter: 0 });
  R.push({ title: "Unsorted array", action: "Start", line: 0, m: `Heap sort first turns the array into a ${T}-heap, then repeatedly moves the ${T === "max" ? "largest" : "smallest"} element to the end.` });
  for (let i = (n >> 1) - 1; i >= 0; i--) {
    R.extra.cur = i;
    R.push({ marks: { cur: [i] }, title: `Build ${T}-heap: heapify index ${i}`, action: "Build", line: 1, m: `Phase 1 builds the heap bottom-up, as in Build Heap.` });
    siftDown(R, i, n, DOWN(1));
  }
  R.extra.cur = null; R.extra.phase = "Sorting";
  if (n) R.push({ marks: { root: [0] }, title: `${T === "max" ? "Max" : "Min"}-heap built — root ${R.a[0].v}`, action: "Heap ready", line: 1, m: `The root is the ${T === "max" ? "largest" : "smallest"} value. It belongs at the end of the sorted output.` });
  for (let end = n - 1; end >= 1; end--) {
    R.extra.iter++;
    sw(R, 0, end);
    R.extra.sortedFrom = end;
    R.push({ marks: { swap: [0, end] }, title: `Moved ${R.a[end].v} to final position ${end}`, action: "Swap root with last", line: 3, m: `The root swaps with index ${end}. Index ${end} is now sorted and leaves the heap.` });
    R.size = end;
    R.push({ title: `Heap size reduced to ${end}`, action: "Shrink heap", line: 4, m: `The heap now covers indices 0..${end - 1}. The new root may violate the property.` });
    if (end > 1) siftDown(R, 0, end, DOWN(5));
  }
  R.size = 0; R.extra.sortedFrom = 0; R.extra.phase = "Done";
  fin(R, "Array successfully sorted", `Every element has been moved to its final place: ${R.a.map((x) => x.v).join(", ")}.`);
  return res(R);
}

function chain(parts) {
  let c = 0, s = 0;
  const steps = [];
  parts.forEach((r) => {
    r.steps.forEach((st) => steps.push({ ...st, cmps: st.cmps + c, swaps: st.swaps + s }));
    c += r.st.c; s += r.st.s;
  });
  return { steps, arr: parts[parts.length - 1].arr, st: { c, s } };
}
const buildNow = (vals, type) => opBuild(mk(vals), type).arr;

function fastDown(a, i, n, type, k) {
  for (;;) {
    const l = 2 * i + 1, r = l + 1;
    if (l >= n) break;
    let c = l;
    if (r < n) { k.c++; if (type === "min" ? a[r] < a[l] : a[r] > a[l]) c = r; }
    k.c++;
    if (type === "min" ? a[c] < a[i] : a[c] > a[i]) { [a[i], a[c]] = [a[c], a[i]]; k.s++; i = c; } else break;
  }
}
function measure(vals) {
  const b = vals.slice(), cb = { c: 0, s: 0 };
  for (let i = (b.length >> 1) - 1; i >= 0; i--) fastDown(b, i, b.length, "min", cb);
  const ins = [], ci = { c: 0, s: 0 };
  for (const v of vals) {
    ins.push(v);
    let i = ins.length - 1;
    while (i > 0) { const p = (i - 1) >> 1; ci.c++; if (ins[i] < ins[p]) { [ins[i], ins[p]] = [ins[p], ins[i]]; ci.s++; i = p; } else break; }
  }
  const s = vals.slice(), cs = { c: 0, s: 0 };
  for (let i = (s.length >> 1) - 1; i >= 0; i--) fastDown(s, i, s.length, "max", cs);
  for (let e = s.length - 1; e > 0; e--) { [s[0], s[e]] = [s[e], s[0]]; cs.s++; fastDown(s, 0, e, "max", cs); }
  return { build: cb, insert: ci, sort: cs, sorted: s };
}
/* ==LOGIC-END== */

/* ============================ STYLE ============================ */
const CSS = `
@import url('https://fonts.googleapis.com/css2?family=Space+Grotesk:wght@400;500;600;700&family=JetBrains+Mono:wght@400;500;700&display=swap');
.hv{--bg:#080a1a;--panel:rgba(255,255,255,.045);--panel2:rgba(255,255,255,.08);--line:rgba(255,255,255,.11);--edge:rgba(160,170,230,.38);--tx:#eef1ff;--mu:#9099c4;--vi:#8b5cf6;--bl:#3b82f6;--cy:#22d3ee;--new:#34d399;--cmp:#fbbf24;--swp:#f472b6;--rem:#f87171;--root:#38bdf8;--cur:#a78bfa;--node:#171c44;--ns:rgba(139,130,255,.55);
 font-family:'Space Grotesk',system-ui,sans-serif;color:var(--tx);min-height:100vh;
 background:radial-gradient(1100px 560px at 8% -10%,rgba(124,58,237,.20),transparent 60%),radial-gradient(900px 520px at 100% 0%,rgba(34,211,238,.12),transparent 55%),var(--bg)}
.hv.light{--bg:#f2f4fc;--panel:rgba(255,255,255,.82);--panel2:rgba(30,40,100,.07);--line:rgba(30,40,100,.15);--edge:rgba(60,70,140,.4);--tx:#151938;--mu:#555e8c;--node:#e6e9fb;--ns:rgba(90,80,200,.55);--cmp:#d97706;--new:#059669;--swp:#db2777;--rem:#dc2626;--root:#0284c7;--cy:#0891b2;
 background:radial-gradient(1100px 560px at 8% -10%,rgba(124,58,237,.12),transparent 60%),var(--bg)}
.hv *{box-sizing:border-box}
.hv .mono{font-family:'JetBrains Mono',ui-monospace,monospace}
.hv .glass{background:var(--panel);border:1px solid var(--line);border-radius:16px;backdrop-filter:blur(14px);-webkit-backdrop-filter:blur(14px)}
.hv .mu{color:var(--mu)} .hv .tcy{color:var(--cy)} .hv .tgr{color:var(--new)} .hv .tre{color:var(--rem)} .hv .tam{color:var(--cmp)}
.hv .btn{display:inline-flex;align-items:center;gap:6px;padding:8px 13px;border-radius:10px;border:1px solid var(--line);background:var(--panel2);color:var(--tx);font:600 13px 'Space Grotesk',sans-serif;cursor:pointer;transition:border-color .15s,transform .15s,background .15s}
.hv .btn:hover:not(:disabled){border-color:var(--cy);transform:translateY(-1px)}
.hv .btn:disabled{opacity:.4;cursor:not-allowed}
.hv .btn-p{background:linear-gradient(135deg,#7c3aed,#2563eb);border-color:transparent;color:#fff}
.hv .btn-c{background:linear-gradient(135deg,#0e7490,#2563eb);border-color:transparent;color:#fff}
.hv .btn-d{border-color:rgba(248,113,113,.5);color:var(--rem)}
.hv .btn-lg{padding:13px 22px;font-size:15px;border-radius:12px}
.hv .inp{background:var(--panel2);border:1px solid var(--line);color:var(--tx);border-radius:10px;padding:8px 12px;font:500 14px 'JetBrains Mono',monospace;min-width:0}
.hv .inp::placeholder{color:var(--mu)}
.hv select.inp{font-family:'Space Grotesk',sans-serif;font-weight:600}
.hv :focus-visible{outline:2px solid var(--cy);outline-offset:2px}
.hv .seg{display:inline-flex;border:1px solid var(--line);border-radius:10px;overflow:hidden}
.hv .segb{padding:7px 13px;font:600 13px 'Space Grotesk',sans-serif;color:var(--mu);background:transparent;border:0;cursor:pointer}
.hv .segb.on{background:linear-gradient(135deg,#7c3aed,#2563eb);color:#fff}
.hv .chip{display:inline-flex;align-items:center;gap:6px;padding:3px 10px;border-radius:999px;border:1px solid var(--line);background:var(--panel2);font-size:12px}
.hv .hn{transition:transform .55s cubic-bezier(.4,0,.2,1);cursor:pointer;outline:none}
.hv .hn:focus-visible circle:first-of-type{stroke:var(--cy);stroke-width:3}
.hv .hc{position:absolute;left:0;top:0;transition:transform .55s cubic-bezier(.4,0,.2,1);cursor:pointer}
.hv .tl{display:flex;gap:8px;text-align:left;width:100%;padding:6px 8px;border-radius:8px;font:500 12px 'Space Grotesk',sans-serif;color:var(--mu);border:1px solid transparent;background:transparent;cursor:pointer}
.hv .tl.done{color:var(--tx)} .hv .tl.cur{background:var(--panel2);border-color:var(--cy);color:var(--tx)}
.hv .pcl{display:block;padding:2px 10px;border-left:3px solid transparent;white-space:pre;font:12.5px 'JetBrains Mono',monospace;color:var(--mu)}
.hv .pcl.on{background:rgba(139,92,246,.24);border-left-color:var(--cur);color:var(--tx)}
.hv .code{background:rgba(0,0,0,.35);border:1px solid var(--line);border-radius:12px;padding:14px;overflow:auto;font:12.5px/1.55 'JetBrains Mono',monospace;color:#dfe5ff;white-space:pre}
.hv.light .code{background:#14183a}
.hv table{border-collapse:collapse;width:100%} .hv th,.hv td{padding:8px 10px;border-bottom:1px solid var(--line);text-align:left;font-size:13px;vertical-align:top} .hv th{color:var(--mu);font-weight:600}
@keyframes pg{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:none}} .hv .page{animation:pg .35s ease}
@keyframes fi{from{opacity:0}to{opacity:1}} .hv .pop{animation:fi .45s ease}
@keyframes pulse{0%,100%{opacity:1}50%{opacity:.35}} .hv .pulse{animation:pulse 1.1s infinite}
@keyframes drift{0%,100%{transform:translateY(0)}50%{transform:translateY(-6px)}} .hv .drift{animation:drift 6s ease-in-out infinite}
@media (prefers-reduced-motion:reduce){.hv *{animation:none!important;transition:none!important}}
`;

/* ============================ SHARED ============================ */
const Ctx = createContext(null);
const useCtx = () => useContext(Ctx);
const KINDS = ["bad", "rem", "swap", "new", "cmp", "cur", "sorted", "root"];
const KCOL = { bad: "var(--rem)", rem: "var(--rem)", swap: "var(--swp)", new: "var(--new)", cmp: "var(--cmp)", cur: "var(--cur)", sorted: "var(--bl)", root: "var(--root)" };
const kindOf = (marks, i) => { for (const k of KINDS) if (marks[k] && marks[k].includes(i)) return k; return null; };
const SPEED = { slow: 1500, normal: 850, fast: 320 };
const orderById = (arr) => arr.map((it, i) => ({ it, i })).filter((x) => x.it).sort((a, b) => a.it.id - b.it.id);
const rndInt = (a, b) => a + Math.floor(Math.random() * (b - a + 1));
const typeName = (t) => (t === "min" ? "Min heap" : "Max heap");

function usePlayer(speedOverride) {
  const { speed: gs } = useCtx();
  const speed = speedOverride || gs;
  const [steps, setSteps] = useState([]);
  const [i, setI] = useState(0);
  const [playing, setPlaying] = useState(false);
  useEffect(() => {
    if (!playing) return;
    const t = setTimeout(() => { if (i >= steps.length - 1) setPlaying(false); else setI((x) => x + 1); }, SPEED[speed]);
    return () => clearTimeout(t);
  }, [playing, i, steps, speed]);
  const load = (s, auto = true) => { setSteps(s); setI(0); setPlaying(auto && s.length > 1); };
  return { steps, i, setI, playing, setPlaying, load, step: steps[i] || null, total: steps.length, atEnd: i >= steps.length - 1 };
}

const Card = ({ title, icon: I, right, children, className = "" }) => (
  <section className={`glass p-4 ${className}`}>
    {(title || right) && (
      <header className="flex items-center justify-between gap-2 mb-3">
        <h3 className="font-semibold text-sm flex items-center gap-2">{I && <I size={16} className="tcy" />}{title}</h3>
        {right}
      </header>
    )}
    {children}
  </section>
);
const PageHead = ({ title, sub, right }) => (
  <div className="flex flex-wrap items-end justify-between gap-3 mb-4">
    <div>
      <h1 className="text-2xl md:text-3xl font-bold tracking-tight">{title}</h1>
      {sub && <p className="mu text-sm mt-1 max-w-2xl">{sub}</p>}
    </div>
    {right}
  </div>
);
const Tile = ({ label, value, tone }) => (
  <div className="glass p-3">
    <div className="text-xs mu">{label}</div>
    <div className={`text-xl font-bold mono mt-0.5 ${tone || ""}`}>{value}</div>
  </div>
);
const Msg = ({ m }) => m ? (
  <p className={`text-sm mt-3 ${m.k === "err" ? "tre" : m.k === "ok" ? "tgr" : "tcy"}`} role="status">{m.k === "err" ? "⚠ " : ""}{m.t}</p>
) : null;
const Seg = ({ value, onChange, options }) => (
  <div className="seg" role="group">
    {options.map(([v, l]) => <button key={v} className={`segb ${value === v ? "on" : ""}`} onClick={() => onChange(v)}>{l}</button>)}
  </div>
);
const TypeSeg = ({ value, onChange }) => <Seg value={value} onChange={onChange} options={[["min", "Min heap"], ["max", "Max heap"]]} />;

function TreeView({ arr, size, marks = {}, sel = null, onSel, rings = {}, showIdx = false, showLevels = false, showProp = false, showLabel = false, type = "min", minLv = 3, empty, rootGlow = true }) {
  const n = size ?? arr.length;
  if (!n) return <div className="mu text-sm text-center py-10 px-4">{empty || "No elements available. Add values to start building your heap."}</div>;
  const items = arr.slice(0, n);
  const Lv = Math.max(levelsOf(n), minLv);
  const W = 720, gap = Lv > 5 ? 60 : 74;
  const r = Lv <= 3 ? 24 : Lv === 4 ? 21 : Lv === 5 ? 17 : 12;
  const H = 30 + (Lv - 1) * gap + 36 + (showLabel ? 10 : 0);
  const pos = (i) => { const d = depthOf(i), k = i + 1 - (1 << d); return [(W * (k + 0.5)) / (1 << d), 28 + d * gap]; };
  return (
    <svg viewBox={`0 0 ${W} ${H}`} className="w-full" style={{ maxHeight: 440 }} role="img" aria-label={`Binary heap tree with ${n} nodes`}>
      {showLevels && Array.from({ length: levelsOf(n) }).map((_, d) => (
        <g key={"lv" + d}>
          <line x1="0" x2={W} y1={28 + d * gap} y2={28 + d * gap} stroke="var(--line)" strokeDasharray="4 6" />
          <text x="4" y={28 + d * gap - 6} style={{ fill: "var(--mu)", fontSize: 11 }} className="mono">level {d}</text>
        </g>
      ))}
      {items.map((it, i) => {
        if (!it || i === 0) return null;
        const p = parentOf(i);
        if (!items[p]) return null;
        const [x1, y1] = pos(p), [x2, y2] = pos(i);
        let col = "var(--edge)";
        if (showProp) col = lt(type, it, items[p]) ? "var(--rem)" : "var(--new)";
        if (sel === i || sel === p) col = "var(--cy)";
        return <line key={"e" + it.id} x1={x1} y1={y1} x2={x2} y2={y2} style={{ stroke: col, strokeWidth: sel === i || sel === p || showProp ? 2.5 : 1.6 }} />;
      })}
      {orderById(items).map(({ it, i }) => {
        const [x, y] = pos(i);
        const k = kindOf(marks, i) || (rootGlow && i === 0 ? "root" : null);
        const col = k ? KCOL[k] : null;
        const s = fmt(it.v);
        const fs = r * (s.length > 3 ? 0.52 : s.length > 2 ? 0.62 : 0.76);
        const ring = rings[i] || (sel === i ? "var(--cy)" : null);
        return (
          <g key={it.id} className="hn" style={{ transform: `translate(${x}px,${y}px)` }} tabIndex={0} role="button"
            aria-label={`Node ${s} at index ${i}`} onClick={() => onSel && onSel(i)}
            onKeyDown={(e) => { if (e.key === "Enter" && onSel) onSel(i); }}>
            <title>{`Value ${it.v} · index ${i}${it.label ? " · " + it.label : ""}`}</title>
            {ring && <circle r={r + 6} style={{ fill: "none", stroke: ring, strokeWidth: 2, strokeDasharray: "4 3" }} />}
            <circle r={r} style={{ fill: "var(--node)", stroke: col || "var(--ns)", strokeWidth: col ? 3 : 1.5 }} />
            {col && <circle r={r} style={{ fill: col, opacity: 0.28 }} />}
            <text textAnchor="middle" dy=".35em" className="mono" style={{ fill: "var(--tx)", fontSize: fs, fontWeight: 700, pointerEvents: "none" }}>{s}</text>
            {showIdx && <text y={-r - 6} textAnchor="middle" className="mono" style={{ fill: "var(--cy)", fontSize: 10, pointerEvents: "none" }}>[{i}]</text>}
            {showLabel && it.label && <text y={r + 13} textAnchor="middle" style={{ fill: "var(--mu)", fontSize: 11, pointerEvents: "none" }}>{it.label.slice(0, 13)}</text>}
          </g>
        );
      })}
    </svg>
  );
}

function ArrayView({ arr, size, marks = {}, sel = null, onSel, sortedFrom, rings = {} }) {
  const n = arr.length, cw = 56;
  if (!n) return <div className="mu text-sm text-center py-4">The array is empty.</div>;
  return (
    <div className="overflow-x-auto pb-2">
      <div className="relative" style={{ width: n * cw, height: 66 }}>
        {orderById(arr).map(({ it, i }) => {
          const inSorted = sortedFrom != null && i >= sortedFrom;
          const dim = size != null && i >= size && !inSorted;
          const k = kindOf(marks, i) || (inSorted ? "sorted" : null) || (i === 0 && !dim ? "root" : null);
          const col = k ? KCOL[k] : null;
          const ring = rings[i] || (sel === i ? "var(--cy)" : null);
          return (
            <div key={it.id} className="hc" style={{ transform: `translateX(${i * cw}px)`, width: cw - 6, opacity: dim ? 0.35 : 1 }}
              onClick={() => onSel && onSel(i)} role="button" tabIndex={0} aria-label={`Array index ${i}, value ${it.v}`}
              onKeyDown={(e) => { if (e.key === "Enter" && onSel) onSel(i); }} title={`Index ${i}`}>
              <div className="mono font-bold text-sm flex items-center justify-center"
                style={{ height: 42, borderRadius: 10, background: col ? `color-mix(in srgb, ${col} 26%, var(--node))` : "var(--node)", border: `2px solid ${ring || col || "var(--ns)"}`, boxShadow: ring ? `0 0 0 2px ${ring}55` : "none" }}>
                {fmt(it.v)}
              </div>
              <div className="mono text-center mu" style={{ fontSize: 11, marginTop: 3 }}>{i}</div>
            </div>
          );
        })}
      </div>
    </div>
  );
}

const LEG = [["new", "New"], ["cmp", "Comparing"], ["swap", "Swapped"], ["rem", "Removed / violation"], ["root", "Min or max"], ["cur", "Current"], ["sorted", "Sorted"]];
const Legend = () => (
  <div className="flex flex-wrap gap-x-3 gap-y-1 text-xs mu mt-2">
    {LEG.map(([k, l]) => <span key={k} className="inline-flex items-center gap-1.5"><i className="inline-block w-2.5 h-2.5 rounded-full" style={{ background: KCOL[k] }} />{l}</span>)}
  </div>
);

function Controls({ p, showSpeed = true }) {
  const { speed, setSpeed } = useCtx();
  return (
    <div className="flex flex-wrap items-center gap-2">
      <button className="btn" disabled={!p.total || p.i === 0} onClick={() => { p.setPlaying(false); p.setI(Math.max(0, p.i - 1)); }}><SkipBack size={14} />Previous</button>
      {p.playing
        ? <button className="btn btn-p" onClick={() => p.setPlaying(false)}><Pause size={14} />Pause</button>
        : <button className="btn btn-p" disabled={!p.total} onClick={() => { if (p.atEnd) p.setI(0); p.setPlaying(true); }}><Play size={14} />{p.atEnd && p.total > 1 ? "Replay" : "Play"}</button>}
      <button className="btn" disabled={!p.total || p.atEnd} onClick={() => { p.setPlaying(false); p.setI(Math.min(p.total - 1, p.i + 1)); }}>Next<SkipForward size={14} /></button>
      {showSpeed && <Seg value={speed} onChange={setSpeed} options={[["slow", "Slow"], ["normal", "Normal"], ["fast", "Fast"]]} />}
      <span className="mono text-xs mu ml-auto">{p.total ? `Step ${p.i + 1} / ${p.total}` : "No steps yet"}</span>
    </div>
  );
}

function Timeline({ p, max = 288 }) {
  const box = useRef(null);
  useEffect(() => {
    const c = box.current && box.current.querySelector(".cur");
    if (c && box.current) box.current.scrollTop = c.offsetTop - box.current.clientHeight / 2;
  }, [p.i, p.steps]);
  return (
    <Card title="Algorithm timeline" icon={Activity}>
      {!p.total ? <p className="mu text-sm">Run an operation and every step will be listed here. Click a step to jump to it.</p> : (
        <ol ref={box} className="space-y-1 overflow-auto relative" style={{ maxHeight: max }}>
          {p.steps.map((s, k) => (
            <li key={k}>
              <button className={`tl ${k === p.i ? "cur" : ""} ${k <= p.i ? "done" : ""}`} onClick={() => { p.setPlaying(false); p.setI(k); }}>
                <span className="mono" style={{ width: 14, color: k <= p.i ? "var(--new)" : "var(--mu)" }}>{k <= p.i ? "✓" : "•"}</span>{s.title}
              </button>
            </li>
          ))}
        </ol>
      )}
    </Card>
  );
}

function OpPanel({ step, idle }) {
  return (
    <Card title="Live operation" icon={Sparkles}>
      {step && step.violation && <div className="chip mb-2 pulse" style={{ borderColor: "var(--rem)", color: "var(--rem)" }}>⚠ Heap property violated</div>}
      <div className="space-y-2.5">
        <div><div className="text-xs mu">Current operation</div><div className="text-sm font-semibold">{step ? step.title : idle || "Waiting for an operation"}</div></div>
        <div className="grid grid-cols-2 gap-3">
          <div><div className="text-xs mu">Comparison</div><div className="mono text-sm tam">{step && step.cmp ? step.cmp : "—"}</div></div>
          <div><div className="text-xs mu">Action</div><div className="text-sm font-semibold">{step && step.action ? step.action : "—"}</div></div>
        </div>
        {step && step.out !== undefined && <div className="text-xs mu">Removed value: <span className="mono tcy font-bold">{step.out}</span></div>}
      </div>
    </Card>
  );
}

function Monitor({ step, arr, size, type }) {
  const viol = validate(arr, type, size);
  const ok = viol.length === 0;
  return (
    <Card title="Heap property monitor" icon={ShieldCheck}>
      <div className="flex items-center gap-2 mb-3">
        <span className={`inline-block w-3 h-3 rounded-full ${ok ? "" : "pulse"}`} style={{ background: ok ? "var(--new)" : "var(--rem)" }} />
        <span className="font-semibold text-sm" style={{ color: ok ? "var(--new)" : "var(--rem)" }}>
          {size === 0 ? "Empty heap" : ok ? "✓ Valid" : "⚠ Heap property violated"}
        </span>
      </div>
      {!ok && <p className="text-xs mu mb-2">{step && !step.done ? "The algorithm is repairing this right now." : viol[0].msg}</p>}
      <div className="grid grid-cols-2 gap-x-4 gap-y-1.5 text-sm">
        {[["Heap type", typeName(type)], ["Root", size ? fmt(arr[0].v) : "—"], ["Nodes checked", step ? step.checked : 0], ["Comparisons", step ? step.cmps : 0], ["Swaps", step ? step.swaps : 0], ["Height", `${levelsOf(size)} levels`]].map(([a, b]) => (
          <React.Fragment key={a}><span className="mu">{a}</span><span className="mono text-right">{b}</span></React.Fragment>
        ))}
      </div>
    </Card>
  );
}

function Mentor({ step, idle }) {
  const text = step ? step.m || step.title : idle || "Run an operation and I will explain each move in plain words.";
  return (
    <Card title="Heap Mentor" icon={GraduationCap}>
      <p className="text-sm leading-relaxed">{text}</p>
      <p className="text-xs mu mt-3">Explanations come from built-in rules for each algorithm step. No AI model is running.</p>
    </Card>
  );
}

function Inspector({ arr, type, sel, onDelete }) {
  if (sel == null || !arr[sel]) return <Card title="Node inspector" icon={Eye}><p className="mu text-sm">Click any node in the tree, or any cell in the array, to inspect it.</p></Card>;
  const n = arr.length, i = sel, p = i ? parentOf(i) : null, l = 2 * i + 1 < n ? 2 * i + 1 : null, r = 2 * i + 2 < n ? 2 * i + 2 : null;
  const ok = (p == null || !lt(type, arr[i], arr[p])) && (l == null || !lt(type, arr[l], arr[i])) && (r == null || !lt(type, arr[r], arr[i]));
  const show = (j) => (j == null ? "—" : `index ${j} (${fmt(arr[j].v)})`);
  const rows = [["Value", fmt(arr[i].v)], ["Index", i], ["Parent", show(p)], ["Left child", show(l)], ["Right child", show(r)], ["Depth", depthOf(i)], ["Level", depthOf(i) + 1], ["Heap status", ok ? "✓ Valid" : "⚠ Violated"], ["Role", i === 0 ? (n === 1 ? "Root (also a leaf)" : "Root") : l == null ? "Leaf node" : "Internal node"]];
  return (
    <Card title="Node inspector" icon={Eye}>
      <div className="grid grid-cols-2 gap-x-3 gap-y-1.5 text-sm">
        {rows.map(([a, b]) => <React.Fragment key={a}><span className="mu">{a}</span><span className="mono text-right" style={a === "Heap status" ? { color: ok ? "var(--new)" : "var(--rem)" } : {}}>{b}</span></React.Fragment>)}
      </div>
      {onDelete && <button className="btn btn-d mt-3" onClick={() => onDelete(i)}><Trash2 size={14} />Delete this node</button>}
    </Card>
  );
}

function heapDna(arr, type) {
  const n = arr.length, lv = levelsOf(n);
  const viol = validate(arr, type).length;
  const order = n > 1 ? Math.round(100 * (1 - viol / (n - 1))) : 100;
  const density = n ? Math.round((100 * n) / (Math.pow(2, lv) - 1)) : 0;
  const sub = (i) => (i >= n ? 0 : 1 + sub(2 * i + 1) + sub(2 * i + 2));
  const h = (i) => (i >= n ? 0 : 1 + Math.max(h(2 * i + 1), h(2 * i + 2)));
  const balance = n > 1 ? 100 - Math.abs(h(1) - h(2)) * 50 : 100;
  return { structure: 100, order, lv, density, balance, sub };
}
function Dna({ arr, type }) {
  const n = arr.length;
  if (!n) return <Card title="Heap DNA" icon={Sparkles}><p className="mu text-sm">Build a heap to see its fingerprint.</p></Card>;
  const d = heapDna(arr, type);
  const vs = arr.map((x) => x.v), mn = Math.min(...vs), mx = Math.max(...vs);
  const cells = Math.min(n, 63), cw = 6, W = 7 * 18;
  const bad = new Set(validate(arr, type).map((v) => v.c));
  return (
    <Card title="Heap DNA" icon={Sparkles}>
      <div className="flex gap-4 items-start">
        <svg viewBox={`0 0 ${W} ${6 * 12 + 4}`} style={{ width: 120, flexShrink: 0 }} role="img" aria-label="Heap fingerprint">
          {arr.slice(0, cells).map((it, i) => {
            const dp = depthOf(i), k = i + 1 - (1 << dp), cnt = 1 << dp, w = W / cnt;
            const t = mx === mn ? 0.5 : (it.v - mn) / (mx - mn);
            return <rect key={it.id} x={k * w + 0.5} y={dp * 12 + 1} width={Math.max(w - 1, 1.5)} height={10} rx={2} fill={`hsl(${250 - t * 120} 75% ${48 + (type === "min" ? t : 1 - t) * 14}%)`} stroke={bad.has(i) ? "var(--rem)" : "none"} strokeWidth="1.5" />;
          })}
        </svg>
        <div className="flex-1 space-y-1.5 text-xs">
          {[["Structure", d.structure, "Complete"], ["Order", d.order, d.order === 100 ? "Valid" : "Broken"], ["Height", Math.min(100, d.lv * 16), `${d.lv} levels`], ["Density", d.density, `${d.density}% full`], ["Balance", d.balance, `${d.balance}%`]].map(([a, v, t]) => (
            <div key={a}>
              <div className="flex justify-between"><span className="mu">{a}</span><span className="mono">{t}</span></div>
              <div style={{ height: 5, borderRadius: 4, background: "var(--panel2)" }}><div style={{ width: `${v}%`, height: 5, borderRadius: 4, background: "linear-gradient(90deg,var(--vi),var(--cy))", transition: "width .5s" }} /></div>
            </div>
          ))}
        </div>
      </div>
    </Card>
  );
}

function StatsPanel({ arr, size, step, ops, cx }) {
  const n = size;
  return (
    <Card title="Live statistics" icon={Activity}>
      <div className="grid grid-cols-2 sm:grid-cols-3 gap-2">
        {[["Heap size", n], ["Height", `${levelsOf(n)} levels`], ["Root value", n ? fmt(arr[0].v) : "—"], ["Leaf nodes", n - (n >> 1)], ["Internal nodes", n >> 1], ["Comparisons", step ? step.cmps : 0], ["Swaps", step ? step.swaps : 0], ["Operations", ops], ["Current complexity", cx || "—"]].map(([a, b]) => (
          <div key={a} className="rounded-lg p-2" style={{ background: "var(--panel2)" }}><div className="text-xs mu">{a}</div><div className="mono font-bold text-sm">{b}</div></div>
        ))}
      </div>
    </Card>
  );
}

function PseudoCode({ pc, step }) {
  if (!pc) return null;
  return (
    <div className="space-y-3">
      <div className="code" style={{ padding: "10px 0" }}>{pc.main.map((t, k) => <span key={k} className={`pcl ${step && step.line === k ? "on" : ""}`}>{t}</span>)}</div>
      {pc.subs && Object.entries(pc.subs).map(([key, lines]) => (
        <div key={key} className="code" style={{ padding: "10px 0" }}>
          {lines.map((t, k) => <span key={k} className={`pcl ${step && step.sub === key && step.sline === k ? "on" : ""}`}>{t}</span>)}
        </div>
      ))}
    </div>
  );
}

/* shared viz bundle: tree + array + controls for a player */
function VizBlock({ p, base, type, sel, setSel, sortedFrom, showTimeline = false }) {
  const step = p.step;
  const arr = step ? step.arr : base;
  const size = step ? step.size : base.length;
  const marks = step ? step.marks : {};
  return (
    <div>
      <TreeView arr={arr} size={size} marks={marks} type={type} sel={sel} onSel={setSel} />
      <div className="mt-2"><ArrayView arr={arr} size={size} marks={marks} sel={sel} onSel={setSel} sortedFrom={sortedFrom} /></div>
      <Legend />
      <div className="mt-3"><Controls p={p} /></div>
    </div>
  );
}

/* ============================ LANDING ============================ */
function HeroHeap() {
  const cur = useRef(buildNow([14, 22, 9, 31, 6, 18, 27, 12, 40, 3], "min"));
  const p = usePlayer("fast");
  const nextOp = () => {
    const a = cur.current;
    const r = a.length >= 12 || (a.length > 6 && Math.random() < 0.45) ? opExtract(a, "min") : opInsert(a, "min", { id: uid(), v: rndInt(1, 45) });
    cur.current = r.arr;
    p.load(r.steps);
  };
  useEffect(() => {
    if (p.playing) return;
    const t = setTimeout(nextOp, p.total ? 1200 : 500);
    return () => clearTimeout(t);
  }, [p.playing]);
  const step = p.step;
  const arr = step ? step.arr : cur.current;
  return (
    <div className="glass p-4 drift">
      <TreeView arr={arr} size={step ? step.size : arr.length} marks={step ? step.marks : {}} minLv={4} />
      <div className="flex items-center gap-2 mt-2 text-xs mu">
        <span className="inline-block w-2 h-2 rounded-full pulse" style={{ background: "var(--new)" }} />
        <span>A real min-heap is running live: <span style={{ color: "var(--tx)" }}>{step ? step.title : "starting…"}</span></span>
      </div>
    </div>
  );
}

function Landing() {
  const { go } = useCtx();
  const why = [
    ["Visual learning", "Understand heap operations through animated tree transformations."],
    ["Real-time experimentation", "Modify the heap and instantly see every structural change."],
    ["Algorithm insight", "Follow each comparison, swap and heapify operation."],
    ["Challenge mode", "Test your DSA knowledge through interactive problems."],
  ];
  const stats = [["1", "Data structure"], ["2", "Heap types"], ["7", "Core operations"], ["9", "Algorithm visualizations"]];
  return (
    <div className="page max-w-6xl mx-auto px-4 sm:px-6 pb-16">
      <div className="flex items-center justify-between py-5">
        <span className="font-bold tracking-widest text-sm">HEAPVERSE</span>
        <button className="btn" onClick={() => go("lab")}>Enter Heap Lab<ChevronRight size={14} /></button>
      </div>
      <div className="grid lg:grid-cols-2 gap-8 items-center py-6 lg:py-12">
        <div>
          <h1 className="font-bold leading-none" style={{ fontSize: "clamp(44px,9vw,92px)", letterSpacing: "-0.03em", background: "linear-gradient(120deg,#c4b5fd,#60a5fa 55%,#22d3ee)", WebkitBackgroundClip: "text", color: "transparent" }}>HEAPVERSE</h1>
          <p className="text-xl mt-3 font-medium">Explore. Build. Break. Understand.</p>
          <p className="mu mt-4 max-w-md leading-relaxed">An interactive laboratory for mastering Heaps, Binary Heaps, Priority Queues and Heap Sort through visualization and experimentation.</p>
          <div className="flex flex-wrap gap-3 mt-7">
            <button className="btn btn-p btn-lg" onClick={() => go("lab")}><FlaskConical size={18} />Enter Heap Lab</button>
            <button className="btn btn-lg" onClick={() => go("learn")}><Compass size={18} />Explore DSA Concepts</button>
          </div>
        </div>
        <HeroHeap />
      </div>
      <div className="grid grid-cols-2 md:grid-cols-4 gap-3 mt-4">
        {stats.map(([n, l]) => (
          <div key={l} className="glass p-4"><div className="text-3xl font-bold mono tcy">{n}</div><div className="text-sm mu mt-1">{l}</div></div>
        ))}
      </div>
      <h2 className="text-2xl font-bold mt-14 mb-4">Why HEAPVERSE?</h2>
      <div className="grid sm:grid-cols-2 lg:grid-cols-4 gap-3">
        {why.map(([t, d]) => (
          <div key={t} className="glass p-4"><h3 className="font-semibold">{t}</h3><p className="mu text-sm mt-2 leading-relaxed">{d}</p></div>
        ))}
      </div>
    </div>
  );
}

/* ============================ DASHBOARD ============================ */
const DEMO = [
  ["lab", "Heap Lab: type 50, 20, 40, 10, 30, 60, 5, pick Min heap, press Build heap."],
  ["lab", "Insert 2 and watch heapify-up carry it to the root."],
  ["lab", "Extract the minimum and watch the root removal and heapify-down."],
  ["lab", "Switch to Max heap: the same data is rebuilt as a max-heap."],
  ["sort", "Heap Sort Arena: sort the same numbers step by step."],
  ["pq", "Priority Queue: add three tasks and process the most urgent one."],
  ["challenge", "Challenge Arena: complete a question."],
  ["journey", "Your Heap Journey: review everything you did."],
];
const MODS = [
  ["lab", "Heap Lab", "Build, insert, extract and delete with animated steps.", FlaskConical],
  ["binary", "Binary Heap", "Complete tree plus heap property, synced with the array.", Network],
  ["heapify", "Heapify", "Heapify engine and bottom-up Build Heap.", Wand2],
  ["sort", "Heap Sort", "Array, heap and sorted output side by side.", ArrowDownUp],
  ["pq", "Priority Queue", "A task scheduler powered by the heap.", ListOrdered],
  ["algo", "Algorithm Explorer", "Pseudocode with live line highlighting.", Compass],
  ["challenge", "Challenge Arena", "Questions, levels and a mastery score.", Trophy],
  ["repair", "Validate & Repair", "Find the violation and fix it yourself.", ShieldCheck],
];
function Dashboard() {
  const { heap, type, stats, go, op } = useCtx();
  return (
    <div>
      <PageHead title="Heap Control Center" sub="Your live heap, your progress and a guided path through the whole lab." />
      <div className="grid grid-cols-2 md:grid-cols-4 xl:grid-cols-6 gap-3 mb-4">
        <Tile label="Heap type" value={typeName(type)} /><Tile label="Nodes" value={heap.length} />
        <Tile label="Root" value={heap.length ? fmt(heap[0].v) : "—"} /><Tile label="Operations" value={stats.ops} />
        <Tile label="Comparisons" value={stats.cmps} /><Tile label="Swaps" value={stats.swaps} />
      </div>
      <div className="grid lg:grid-cols-3 gap-4">
        <Card title="Your current heap" icon={Network} className="lg:col-span-2" right={<button className="btn" onClick={() => go("lab")}>Open Heap Lab<ChevronRight size={14} /></button>}>
          <TreeView arr={heap} type={type} empty="No elements available. Open the Heap Lab and add values to start building your heap." />
          {heap.length > 0 && <div className="mt-2"><ArrayView arr={heap} /></div>}
        </Card>
        <Dna arr={heap} type={type} />
      </div>
      <h2 className="font-semibold mt-6 mb-3">Guided demo</h2>
      <div className="grid md:grid-cols-2 gap-2">
        {DEMO.map(([pg, t], k) => (
          <button key={k} onClick={() => go(pg)} className="glass p-3 text-left flex gap-3 items-start" style={{ cursor: "pointer", color: "inherit" }}>
            <span className="mono tcy text-sm mt-0.5">{k + 1}</span><span className="text-sm">{t}</span>
          </button>
        ))}
      </div>
      <h2 className="font-semibold mt-6 mb-3">Modules</h2>
      <div className="grid sm:grid-cols-2 xl:grid-cols-4 gap-3">
        {MODS.map(([pg, t, d, I]) => (
          <button key={pg} onClick={() => go(pg)} className="glass p-4 text-left" style={{ cursor: "pointer", color: "inherit" }}>
            <I size={20} className="tcy" /><div className="font-semibold mt-2">{t}</div><div className="mu text-sm mt-1">{d}</div>
          </button>
        ))}
      </div>
    </div>
  );
}

/* ============================ HEAP LAB ============================ */
const TOO_MANY = "The lab draws up to 63 nodes (6 levels). Remove some elements first.";
function HeapLab() {
  const { heap, setHeap, type, setType, labInput: inp, setLabInput: setInp, bump, setOp, stats } = useCtx();
  const p = usePlayer();
  const [msg, setMsg] = useState(null);
  const [sel, setSel] = useState(null);
  const [cnt, setCnt] = useState(10);
  const [last, setLast] = useState("—");
  const step = p.step;
  const arr = step ? step.arr : heap;
  const size = step ? step.size : heap.length;
  const marks = step ? step.marks : {};
  useEffect(() => { setOp((o) => ({ ...o, busy: p.playing })); }, [p.playing]);

  const run = (r, name, cx, exp) => {
    setHeap(r.arr); p.load(r.steps); setSel(null); setLast(cx);
    setOp({ name, busy: true });
    bump({ ops: 1, cmps: r.st.c, swaps: r.st.s, explore: exp });
  };
  const readVals = () => {
    if (!inp.trim()) { setMsg({ k: "err", t: "Enter at least one number first, for example 10, 4, 15." }); return null; }
    const { vals, bad } = parseVals(inp);
    if (bad.length) { setMsg({ k: "err", t: `${bad.slice(0, 3).map((b) => `"${b}"`).join(", ")} ${bad.length > 1 ? "are" : "is"} not a number. Use numbers separated by commas.` }); return null; }
    if (vals.some((v) => Math.abs(v) > 1e9)) { setMsg({ k: "err", t: "Values must stay between -1,000,000,000 and 1,000,000,000." }); return null; }
    return vals;
  };
  const empty = (verb) => { setMsg({ k: "err", t: `No elements available. Add values to start building your heap${verb ? ` before you ${verb}` : ""}.` }); };
  const doInsert = () => {
    const vals = readVals(); if (!vals) return;
    if (heap.length + vals.length > 63) { setMsg({ k: "err", t: TOO_MANY }); return; }
    let cur = heap; const parts = [];
    vals.forEach((v) => { const r = opInsert(cur, type, { id: uid(), v }); parts.push(r); cur = r.arr; });
    run(chain(parts), `Insert ${vals.join(", ")}`, "O(log n)", "Insert");
    bump({ processed: vals.length });
    const dup = new Set([...heap.map((x) => x.v), ...vals]).size < heap.length + vals.length;
    setMsg({ k: "ok", t: `Inserting ${vals.length} value${vals.length > 1 ? "s" : ""}.${dup ? " Duplicates are allowed: equal values never trigger a swap." : ""}` });
    setInp("");
  };
  const doBuild = () => {
    let items;
    if (inp.trim()) { const vals = readVals(); if (!vals) return; if (vals.length > 63) { setMsg({ k: "err", t: TOO_MANY }); return; } items = mk(vals); }
    else if (heap.length) items = heap;
    else return empty();
    run(opBuild(items, type), "Build heap", "O(n)", "Build Heap");
    bump({ processed: items.length });
    setMsg({ k: "ok", t: `Building a ${type}-heap from ${items.length} values, bottom-up.` });
  };
  const doExtract = () => {
    if (!heap.length) return setMsg({ k: "err", t: "Cannot extract from an empty heap. Add values to start building your heap." });
    run(opExtract(heap, type), `Extract ${type}`, "O(log n)", type === "min" ? "Extract Min" : "Extract Max");
    setMsg({ k: "ok", t: `Extracting the ${type === "min" ? "minimum" : "maximum"}: ${heap[0].v}.` });
  };
  const doDelete = (idx) => {
    if (!heap.length) return setMsg({ k: "err", t: "Cannot delete from an empty heap. Add values to start building your heap." });
    run(opDeleteAt(heap, type, idx), idx === 0 ? "Delete root" : `Delete index ${idx}`, "O(log n)", "Delete");
    setMsg({ k: "ok", t: `Deleting ${heap[idx].v}.` });
  };
  const doPeek = () => {
    if (!heap.length) return empty();
    setLast("O(1)"); setSel(0);
    p.load([{ marks: { root: [0] }, arr: heap, size: heap.length, title: `Peek: the ${type === "min" ? "minimum" : "maximum"} is ${heap[0].v}`, action: "Read root", cmps: 0, swaps: 0, checked: 1, done: true, m: `Peek reads index 0 without changing anything, so it costs O(1).` }], false);
    setMsg({ k: "ok", t: `Peek → ${heap[0].v}. Nothing was removed.` });
    bump({ ops: 1 });
  };
  const doClear = () => { setHeap([]); p.load([]); setSel(null); setLast("—"); setMsg({ k: "info", t: "Heap cleared. Add values to start again." }); };
  const doRandom = () => {
    const r = opBuild(mk(Array.from({ length: cnt }, () => rndInt(1, 100))), type);
    run(r, `Random heap (${cnt})`, "O(n)", "Build Heap"); bump({ processed: cnt });
    setMsg({ k: "ok", t: `Generated ${cnt} random values (1–100) and built a ${type}-heap.` });
  };
  const doReset = () => { setHeap([]); p.load([]); setSel(null); setLast("—"); setInp("50, 20, 40, 10, 30, 60, 5"); setType("min"); setMsg({ k: "info", t: "Lab reset. Your journey statistics are kept." }); };
  const switchType = (t) => {
    if (t === type) return;
    setType(t);
    if (heap.length > 1) { run(opBuild(heap, t), `Rebuild as ${t}-heap`, "O(n)", "Build Heap"); setMsg({ k: "info", t: `Switched to a ${t}-heap: the same values are re-heapified.` }); }
  };

  return (
    <div>
      <PageHead title="Heap Lab" sub="Every operation runs on the real array and is animated one step at a time." />
      <Card>
        <div className="flex flex-wrap items-center gap-2">
          <TypeSeg value={type} onChange={switchType} />
          <input className="inp flex-1" style={{ minWidth: 200 }} value={inp} onChange={(e) => setInp(e.target.value)} onKeyDown={(e) => e.key === "Enter" && doInsert()} placeholder="Enter values: 10, 4, 15, 2, 8, 20, 1" aria-label="Values to insert" />
          <button className="btn btn-p" onClick={doInsert} title="Add the value(s) at the end and heapify up"><Plus size={14} />Insert</button>
          <button className="btn btn-c" onClick={doBuild} title="Bottom-up build, O(n)"><Wand2 size={14} />Build heap</button>
        </div>
        <div className="flex flex-wrap items-center gap-2 mt-3">
          <button className="btn" onClick={() => doDelete(0)} title="Remove the root and heapify down"><Trash2 size={14} />Delete root</button>
          <button className="btn" onClick={doExtract} title="Remove and return the root">Extract {type}</button>
          <button className="btn" onClick={doPeek} title="Read the root, O(1)"><Eye size={14} />Peek</button>
          <button className="btn btn-d" onClick={doClear}><X size={14} />Clear</button>
          <span className="mx-1" style={{ width: 1, height: 22, background: "var(--line)" }} />
          <select className="inp" value={cnt} onChange={(e) => setCnt(+e.target.value)} aria-label="Random heap size"><option value={10}>10 nodes</option><option value={20}>20 nodes</option><option value={50}>50 nodes</option></select>
          <button className="btn" onClick={doRandom}><Shuffle size={14} />Randomize</button>
          <button className="btn" onClick={doReset}><RotateCcw size={14} />Reset lab</button>
        </div>
        <Msg m={msg} />
      </Card>
      <div className="grid xl:grid-cols-3 gap-4 mt-4">
        <div className="xl:col-span-2 space-y-4">
          <Card title="Tree view and array view" icon={Network}>
            <VizBlock p={p} base={heap} type={type} sel={sel} setSel={setSel} />
          </Card>
          <div className="grid md:grid-cols-3 gap-4">
            <Inspector arr={arr} type={type} sel={sel} onDelete={doDelete} />
            <Dna arr={arr} type={type} />
            <StatsPanel arr={arr} size={size} step={step} ops={stats.ops} cx={last} />
          </div>
        </div>
        <div className="space-y-4">
          <OpPanel step={step} />
          <Timeline p={p} />
          <Monitor step={step} arr={arr} size={size} type={type} />
          <Mentor step={step} />
        </div>
      </div>
    </div>
  );
}

/* ============================ BINARY HEAP ============================ */
const CT_OK = mk([1, 2, 3, 4, 5, 6]);
const CT_BAD = [...mk([1, 2, 3]), null, ...mk([5, 6])];
const ORD_OK = buildNow([2, 5, 3, 9, 6, 4], "min");
const ORD_BAD = mk([2, 5, 3, 1, 6, 4]);
function BinaryHeapPage() {
  const [type, setType] = useState("min");
  const [txt, setTxt] = useState("3, 8, 5, 12, 9, 7, 15, 20");
  const [arr, setArr] = useState(() => buildNow([3, 8, 5, 12, 9, 7, 15, 20], "min"));
  const [sel, setSel] = useState(null);
  const [tg, setTg] = useState({ parent: true, children: true, levels: false, idx: true, prop: true });
  const [ix, setIx] = useState("3");
  const [msg, setMsg] = useState(null);
  const n = arr.length;
  const apply = () => {
    const { vals, bad } = parseVals(txt);
    if (!vals.length || bad.length) return setMsg({ k: "err", t: "Enter numbers separated by commas, for example 3, 8, 5, 12." });
    if (vals.length > 31) return setMsg({ k: "err", t: "This explorer shows up to 31 nodes." });
    setArr(buildNow(vals, type)); setSel(null); setMsg({ k: "ok", t: `Built a ${type}-heap from ${vals.length} values.` });
  };
  const rings = {};
  if (sel != null) {
    if (tg.parent && sel > 0) rings[parentOf(sel)] = "var(--vi)";
    if (tg.children) [2 * sel + 1, 2 * sel + 2].forEach((c) => { if (c < n) rings[c] = "var(--bl)"; });
  }
  const iv = /^\d+$/.test(ix.trim()) ? parseInt(ix, 10) : null;
  const L = iv != null ? 2 * iv + 1 : null, Rr = iv != null ? 2 * iv + 2 : null;
  const show = (j) => (j == null ? "—" : j < n ? `${j}  (value ${fmt(arr[j].v)})` : `${j}  (no node)`);
  const T = ({ k, l }) => <label className="chip" style={{ cursor: "pointer" }}><input type="checkbox" checked={tg[k]} onChange={() => setTg({ ...tg, [k]: !tg[k] })} />{l}</label>;
  return (
    <div>
      <PageHead title="Binary Heap Explorer" sub="What makes a binary heap different? Two independent properties that must hold together." />
      <div className="grid lg:grid-cols-3 gap-3 items-stretch">
        <Card title="Structural property" icon={Network}>
          <p className="text-sm mu mb-2">Complete binary tree: every level is full except possibly the last, which fills left to right.</p>
          <div className="grid grid-cols-2 gap-2">
            <div><TreeView arr={CT_OK} minLv={3} rootGlow={false} /><div className="text-xs tgr text-center">✓ complete</div></div>
            <div><TreeView arr={CT_BAD} minLv={3} rootGlow={false} /><div className="text-xs tre text-center">✕ gap at index 3</div></div>
          </div>
        </Card>
        <Card title="Order property" icon={ArrowDownUp}>
          <p className="text-sm mu mb-2">Heap property: in a min-heap every parent is ≤ its children (in a max-heap, ≥).</p>
          <div className="grid grid-cols-2 gap-2">
            <div><TreeView arr={ORD_OK} showProp rootGlow={false} /><div className="text-xs tgr text-center">✓ parents ≤ children</div></div>
            <div><TreeView arr={ORD_BAD} showProp rootGlow={false} /><div className="text-xs tre text-center">✕ 5 &gt; child 1</div></div>
          </div>
        </Card>
        <Card title="Complete tree + heap property" icon={Sparkles}>
          <p className="text-2xl font-bold leading-snug mt-1">Binary heap</p>
          <p className="text-sm mu mt-2">Because the tree is complete it fits in an array with no gaps. Because of the order property the best element is always at index 0.</p>
        </Card>
      </div>
      <Card className="mt-4" title="Interactive heap" icon={Network}
        right={<div className="flex gap-2 flex-wrap"><TypeSeg value={type} onChange={(t) => { setType(t); setArr(buildNow(arr.map((x) => x.v), t)); }} /></div>}>
        <div className="flex flex-wrap gap-2 mb-3">
          <input className="inp flex-1" style={{ minWidth: 200 }} value={txt} onChange={(e) => setTxt(e.target.value)} onKeyDown={(e) => e.key === "Enter" && apply()} aria-label="Heap values" />
          <button className="btn btn-p" onClick={apply}>Build heap</button>
        </div>
        <Msg m={msg} />
        <div className="flex flex-wrap gap-2 my-3">
          <T k="parent" l="Show parent" /><T k="children" l="Show children" /><T k="levels" l="Show levels" /><T k="idx" l="Show array index" /><T k="prop" l="Show heap property" />
        </div>
        <TreeView arr={arr} type={type} sel={sel} onSel={setSel} rings={rings} showIdx={tg.idx} showLevels={tg.levels} showProp={tg.prop} />
        <div className="mt-2"><ArrayView arr={arr} sel={sel} onSel={setSel} rings={rings} /></div>
        <p className="text-xs mu mt-1">Click a node or an array cell: both views highlight the same element. Violet ring = parent, blue rings = children.</p>
      </Card>
      <div className="grid md:grid-cols-2 gap-4 mt-4">
        <Card title="Index formulas (zero-based)" icon={Code2}>
          <div className="space-y-2 mono text-sm">
            <div className="flex justify-between"><span className="mu">Parent</span><span>floor((i - 1) / 2)</span></div>
            <div className="flex justify-between"><span className="mu">Left child</span><span>2i + 1</span></div>
            <div className="flex justify-between"><span className="mu">Right child</span><span>2i + 2</span></div>
          </div>
          {sel != null && n > sel && <p className="text-sm mt-3">Selected index <b className="mono tcy">{sel}</b>: parent {sel ? parentOf(sel) : "—"}, left {2 * sel + 1 < n ? 2 * sel + 1 : "—"}, right {2 * sel + 2 < n ? 2 * sel + 2 : "—"}.</p>}
        </Card>
        <Card title="Index explorer" icon={Compass}>
          <div className="flex gap-2 items-center">
            <label className="text-sm mu" htmlFor="ixi">Index i</label>
            <input id="ixi" className="inp" style={{ width: 90 }} value={ix} onChange={(e) => setIx(e.target.value)} inputMode="numeric" />
            <button className="btn" disabled={iv == null || iv >= n} onClick={() => setSel(iv)}>Show in tree</button>
          </div>
          {iv == null ? <p className="tre text-sm mt-3">Enter a whole number 0 or higher.</p> : (
            <div className="mono text-sm mt-3 space-y-1">
              <div>Parent: {iv === 0 ? "none (root)" : show(parentOf(iv))}</div>
              <div>Left child: {show(L)}</div>
              <div>Right child: {show(Rr)}</div>
            </div>
          )}
        </Card>
      </div>
    </div>
  );
}

/* ============================ MIN vs MAX ============================ */
function ComparePage() {
  const { bump } = useCtx();
  const [txt, setTxt] = useState("12, 7, 25, 3, 18, 10");
  const [fin2, setFin] = useState(null);
  const [msg, setMsg] = useState(null);
  const p = usePlayer();
  const build = (silent) => {
    const { vals, bad } = parseVals(txt);
    if (!vals.length || bad.length) return setMsg({ k: "err", t: "Enter numbers separated by commas, for example 12, 7, 25, 3." });
    if (vals.length > 31) return setMsg({ k: "err", t: "This page shows up to 31 nodes." });
    setMsg(null);
    const items = mk(vals), a = opBuild(items, "min"), b = opBuild(items, "max");
    const L = Math.max(a.steps.length, b.steps.length);
    p.load(Array.from({ length: L }, (_, k) => ({ a: a.steps[Math.min(k, a.steps.length - 1)], b: b.steps[Math.min(k, b.steps.length - 1)], title: `Step ${k + 1}` })));
    setFin({ min: a.arr, max: b.arr });
    if (!silent) bump({ ops: 2, cmps: a.st.c + b.st.c, swaps: a.st.s + b.st.s, processed: vals.length * 2, explore: "Build Heap" });
  };
  useEffect(() => { build(true); }, []);
  const rows = [
    ["Root", "Smallest element", "Largest element"],
    ["Ordering rule", "parent ≤ children", "parent ≥ children"],
    ["Highest priority", "Smallest value (index 0)", "Largest value (index 0)"],
    ["Lowest priority", "Somewhere among the leaves", "Somewhere among the leaves"],
    ["Insert", "O(log n): sift up while smaller than parent", "O(log n): sift up while larger than parent"],
    ["Delete", "O(log n): replace with last, then repair", "O(log n): replace with last, then repair"],
    ["Extract", "extractMin in O(log n)", "extractMax in O(log n)"],
    ["Applications", "Dijkstra, scheduling by deadline, event simulation", "Heap sort (ascending), top-K largest, max-profit jobs"],
  ];
  const side = (key, label) => {
    const st = p.step ? p.step[key === "min" ? "a" : "b"] : null;
    const arr = st ? st.arr : fin2 ? fin2[key] : [];
    return (
      <Card title={label} icon={Network}>
        <TreeView arr={arr} size={st ? st.size : arr.length} marks={st ? st.marks : {}} type={key} minLv={3} />
        <div className="mt-2"><ArrayView arr={arr} size={st ? st.size : arr.length} marks={st ? st.marks : {}} /></div>
        <p className="text-xs mu mt-1 min-h-[2.5em]">{st ? st.title : ""}</p>
        <div className="text-xs mu">Root: <span className="mono tcy font-bold">{arr.length ? fmt(arr[0].v) : "—"}</span> · Swaps: <span className="mono">{st ? st.swaps : 0}</span></div>
      </Card>
    );
  };
  return (
    <div>
      <PageHead title="Min Heap vs Max Heap" sub="The same dataset, built into two different heaps at the same time." />
      <Card>
        <div className="flex flex-wrap gap-2">
          <input className="inp flex-1" style={{ minWidth: 200 }} value={txt} onChange={(e) => setTxt(e.target.value)} onKeyDown={(e) => e.key === "Enter" && build()} aria-label="Dataset" />
          <button className="btn btn-p" onClick={() => build()}><Wand2 size={14} />Build both</button>
        </div>
        <Msg m={msg} />
        <div className="mt-3"><Controls p={p} /></div>
      </Card>
      <div className="grid lg:grid-cols-2 gap-4 mt-4">{side("min", "Min heap")}{side("max", "Max heap")}</div>
      <Card className="mt-4 overflow-x-auto" title="Comparison" icon={GitCompare}>
        <table><thead><tr><th></th><th>Min heap</th><th>Max heap</th></tr></thead>
          <tbody>{rows.map(([a, b, c]) => <tr key={a}><td className="font-semibold">{a}</td><td>{b}</td><td>{c}</td></tr>)}</tbody></table>
      </Card>
    </div>
  );
}

/* ============================ HEAPIFY / BUILD HEAP ============================ */
const FLOW = ["Unordered array", "Select subtree", "Compare children", "Compare with node", "Swap", "Continue downward", "Heap restored"];
function HeapifyPage() {
  const [tab, setTab] = useState("engine");
  return (
    <div>
      <PageHead title={tab === "engine" ? "Heapify Engine" : "Build Heap"} sub={tab === "engine" ? "Sink one node down its subtree until the heap property holds." : "Heapify every non-leaf node, from the last one up to the root."}
        right={<Seg value={tab} onChange={setTab} options={[["engine", "Heapify engine"], ["build", "Build heap"]]} />} />
      <Runner key={tab} mode={tab} />
    </div>
  );
}
function Runner({ mode }) {
  const { bump, setOp } = useCtx();
  const eng = mode === "engine";
  const [txt, setTxt] = useState(eng ? "10, 5, 30, 2, 8, 15, 20" : "45, 12, 78, 23, 9, 34, 67");
  const [at, setAt] = useState("0");
  const [base, setBase] = useState(() => mk(eng ? [10, 5, 30, 2, 8, 15, 20] : [45, 12, 78, 23, 9, 34, 67]));
  const [type, setType] = useState("min");
  const [msg, setMsg] = useState(null);
  const [sel, setSel] = useState(null);
  const p = usePlayer();
  const step = p.step;
  const arr = step ? step.arr : base;
  const go = (t, replay) => {
    const { vals, bad } = parseVals(txt);
    if (!vals.length) return setMsg({ k: "err", t: "No elements available. Enter numbers such as 10, 5, 30, 2." });
    if (bad.length) return setMsg({ k: "err", t: `"${bad[0]}" is not a number. Use numbers separated by commas.` });
    if (vals.length > 31) return setMsg({ k: "err", t: "This lab shows up to 31 nodes." });
    const items = replay ? base : mk(vals);
    const i = parseInt(at, 10);
    if (eng && (!(i >= 0) || i >= vals.length)) return setMsg({ k: "err", t: `Choose an index between 0 and ${vals.length - 1}.` });
    if (eng && 2 * i + 1 >= vals.length) setMsg({ k: "info", t: `Index ${i} is a leaf, so heapify has nothing to do. Try a smaller index.` }); else setMsg(null);
    setType(t); setBase(items); setSel(null);
    const r = eng ? opHeapifyAt(items, t, eng ? i : 0) : opBuild(items, t);
    p.load(r.steps);
    setOp({ name: eng ? `${t}-heapify at ${i}` : `Build ${t}-heap`, busy: true });
    bump({ ops: 1, cmps: r.st.c, swaps: r.st.s, processed: vals.length, explore: eng ? "Heapify" : "Build Heap" });
  };
  useEffect(() => { setOp((o) => ({ ...o, busy: p.playing })); }, [p.playing]);
  const ph = step && step.ph != null ? step.ph : step && step.done ? 6 : 0;
  const kid = step && step.kid != null ? step.kid : null;
  return (
    <div className="grid xl:grid-cols-3 gap-4">
      <div className="xl:col-span-2 space-y-4">
        <Card>
          <div className="flex flex-wrap gap-2 items-center">
            <input className="inp flex-1" style={{ minWidth: 200 }} value={txt} onChange={(e) => setTxt(e.target.value)} aria-label="Array" />
            {eng && <><label className="text-sm mu" htmlFor="hat">at index</label><input id="hat" className="inp" style={{ width: 70 }} value={at} onChange={(e) => setAt(e.target.value)} inputMode="numeric" /></>}
            <button className="btn btn-p" onClick={() => go("min")}><Wand2 size={14} />{eng ? "Min heapify" : "Build min heap"}</button>
            <button className="btn btn-c" onClick={() => go("max")}><Wand2 size={14} />{eng ? "Max heapify" : "Build max heap"}</button>
            <button className="btn" disabled={!p.total} onClick={() => go(type, true)}><Eye size={14} />Watch algorithm</button>
          </div>
          {eng && <p className="text-xs mu mt-2">Heapify assumes the subtrees below the chosen index are already heaps. To fix a whole array use Build heap.</p>}
          <Msg m={msg} />
        </Card>
        {eng && (
          <div className="flex flex-wrap gap-1.5 items-center text-xs">
            {FLOW.map((f, k) => <React.Fragment key={f}><span className="chip" style={k === ph ? { borderColor: "var(--cur)", background: "rgba(139,92,246,.25)" } : { opacity: 0.6 }}>{f}</span>{k < FLOW.length - 1 && <ChevronRight size={12} className="mu" />}</React.Fragment>)}
          </div>
        )}
        <Card title={eng ? "Subtree view" : "Bottom-up construction"} icon={Network}>
          <VizBlock p={p} base={base} type={type} sel={sel} setSel={setSel} />
        </Card>
        {!eng && (
          <Card title="Build state" icon={Activity}>
            <div className="grid grid-cols-2 sm:grid-cols-3 gap-2">
              {[["Current index", step && step.cur != null ? step.cur : "—"], ["Current node", step && step.cur != null && arr[step.cur] ? fmt(arr[step.cur].v) : "—"], ["Selected child", kid != null && arr[kid] ? `${fmt(arr[kid].v)} (index ${kid})` : "—"], ["Comparison", step && step.cmp ? step.cmp : "—"], ["Swap", step && step.action ? step.action : "—"], ["Final state", step && step.done ? "✓ Heap" : "In progress"], ["Comparisons", step ? step.cmps : 0], ["Swaps", step ? step.swaps : 0]].map(([a, b]) => (
                <div key={a} className="rounded-lg p-2" style={{ background: "var(--panel2)" }}><div className="text-xs mu">{a}</div><div className="mono font-bold text-sm">{b}</div></div>
              ))}
            </div>
          </Card>
        )}
      </div>
      <div className="space-y-4">
        <OpPanel step={step} />
        <Timeline p={p} />
        <Monitor step={step} arr={arr} size={step ? step.size : base.length} type={type} />
        <Mentor step={step} />
      </div>
    </div>
  );
}

/* ============================ HEAP SORT ============================ */
function SortPage() {
  const { bump, setOp } = useCtx();
  const [txt, setTxt] = useState("50, 20, 40, 10, 30, 60, 5");
  const [dir, setDir] = useState("asc");
  const [base, setBase] = useState(() => mk([50, 20, 40, 10, 30, 60, 5]));
  const [msg, setMsg] = useState(null);
  const [done, setDone] = useState(false);
  const p = usePlayer();
  const step = p.step;
  const arr = step ? step.arr : base;
  const n = base.length;
  const sf = step ? step.sortedFrom : n;
  const T = dir === "asc" ? "max" : "min";
  useEffect(() => { setOp((o) => ({ ...o, busy: p.playing })); }, [p.playing]);
  const start = (replay) => {
    const { vals, bad } = parseVals(txt);
    if (!vals.length) return setMsg({ k: "err", t: "No elements available. Enter numbers to sort, for example 50, 20, 40, 10." });
    if (bad.length) return setMsg({ k: "err", t: `"${bad[0]}" is not a number.` });
    if (vals.length > 31) return setMsg({ k: "err", t: "The arena shows up to 31 numbers." });
    setMsg(null);
    const items = replay ? base : mk(vals);
    setBase(items);
    const r = opSort(items, dir);
    p.load(r.steps); setOp({ name: "Heap sort", busy: true });
    bump({ ops: 1, cmps: r.st.c, swaps: r.st.s, processed: vals.length, explore: "Heap Sort" });
  };
  const randomize = () => { const v = Array.from({ length: 10 }, () => rndInt(1, 99)); setTxt(v.join(", ")); setBase(mk(v)); p.load([]); setMsg(null); };
  const pct = step ? (step.done ? 100 : Math.round((100 * (n - step.sortedFrom)) / n)) : 0;
  const finished = step && step.done;
  return (
    <div>
      <PageHead title="Heap Sort Arena" sub="Build a heap, move the root to the end, shrink the heap, repeat." />
      <Card>
        <div className="flex flex-wrap gap-2 items-center">
          <input className="inp flex-1" style={{ minWidth: 200 }} value={txt} onChange={(e) => setTxt(e.target.value)} aria-label="Numbers to sort" />
          <Seg value={dir} onChange={(d) => { setDir(d); p.load([]); }} options={[["asc", "Ascending (max-heap)"], ["desc", "Descending (min-heap)"]]} />
          <button className="btn btn-p" onClick={() => start(false)}><ArrowDownUp size={14} />Sort</button>
          <button className="btn" onClick={randomize}><Shuffle size={14} />Random 10</button>
          <button className="btn" disabled={!p.total} onClick={() => start(true)}><RotateCcw size={14} />Restart</button>
        </div>
        <Msg m={msg} />
        <div className="mt-3"><Controls p={p} /></div>
      </Card>
      <div className="grid xl:grid-cols-3 gap-4 mt-4">
        <div className="xl:col-span-2 space-y-4">
          <Card title="1 · Array" icon={Boxes}>
            <ArrayView arr={arr} size={step ? step.size : n} marks={step ? step.marks : {}} sortedFrom={sf} />
          </Card>
          <Card title="2 · Heap" icon={Network}>
            <TreeView arr={arr} size={step ? step.size : n} marks={step ? step.marks : {}} type={T} empty="The heap is empty: every element has moved to the sorted output." />
          </Card>
          <Card title="3 · Sorted output" icon={Check}>
            <div className="flex flex-wrap gap-2">
              {Array.from({ length: n }).map((_, j) => {
                const filled = step ? j >= sf : false;
                return <div key={j} className="mono font-bold flex items-center justify-center" style={{ width: 46, height: 40, borderRadius: 10, border: `2px ${filled ? "solid" : "dashed"} ${filled ? "var(--bl)" : "var(--line)"}`, background: filled ? "color-mix(in srgb, var(--bl) 22%, var(--node))" : "transparent" }}>{filled ? fmt(arr[j].v) : ""}</div>;
              })}
            </div>
            {finished && <p className="tgr font-semibold mt-3">✓ Array successfully sorted</p>}
          </Card>
        </div>
        <div className="space-y-4">
          <Card title="Sort progress" icon={Activity}>
            <div className="flex justify-between text-sm mb-1"><span className="mu">{step ? step.phase : "Ready"}</span><span className="mono">{pct}%</span></div>
            <div style={{ height: 10, borderRadius: 6, background: "var(--panel2)" }} role="progressbar" aria-valuenow={pct} aria-valuemin={0} aria-valuemax={100}><div style={{ width: `${pct}%`, height: 10, borderRadius: 6, background: "linear-gradient(90deg,var(--vi),var(--cy))", transition: "width .4s" }} /></div>
            <div className="grid grid-cols-3 gap-2 mt-3 text-center">
              {[["Comparisons", step ? step.cmps : 0], ["Swaps", step ? step.swaps : 0], ["Iterations", step ? step.iter : 0]].map(([a, b]) => <div key={a} className="rounded-lg p-2" style={{ background: "var(--panel2)" }}><div className="text-xs mu">{a}</div><div className="mono font-bold">{b}</div></div>)}
            </div>
          </Card>
          <OpPanel step={step} />
          <Timeline p={p} max={220} />
          <Mentor step={step} />
        </div>
      </div>
    </div>
  );
}

/* ============================ PRIORITY QUEUE ============================ */
const SAMPLE_TASKS = [["Emergency Patient", 1], ["Database Backup", 3], ["Student Request", 5]];
function PQPage() {
  const { bump, setOp } = useCtx();
  const [heap, setHeap] = useState([]);
  const [done, setDone] = useState([]);
  const [name, setName] = useState("");
  const [pri, setPri] = useState("3");
  const [arr, setArr] = useState("");
  const [tick, setTick] = useState(1);
  const [rm, setRm] = useState("");
  const [msg, setMsg] = useState(null);
  const [incoming, setIncoming] = useState(null);
  const p = usePlayer();
  const step = p.step;
  const view = step ? step.arr : heap;
  useEffect(() => { setOp((o) => ({ ...o, busy: p.playing })); }, [p.playing]);
  useEffect(() => { if (!p.playing) setIncoming(null); }, [p.playing]);
  const addTasks = (list) => {
    let cur = heap, t = tick; const parts = [];
    for (const [nm, pr, at] of list) { const r = opInsert(cur, "min", { id: uid(), v: pr, t: at ?? t, label: nm }); parts.push(r); cur = r.arr; t = (at ?? t) + 1; }
    const r = chain(parts);
    setHeap(r.arr); p.load(r.steps); setTick(t); setArr(""); setIncoming(list.map((x) => x[0]).join(", "));
    bump({ ops: list.length, cmps: r.st.c, swaps: r.st.s, processed: list.length, explore: "Insert" }); setOp({ name: "Add task", busy: true });
  };
  const add = () => {
    const pv = Number(pri), at = arr.trim() === "" ? undefined : Number(arr);
    if (!name.trim()) return setMsg({ k: "err", t: "Give the task a name, for example Database Backup." });
    if (!Number.isInteger(pv) || pv < 1 || pv > 99) return setMsg({ k: "err", t: "Priority must be a whole number from 1 to 99. Lower numbers are more urgent." });
    if (at !== undefined && !Number.isFinite(at)) return setMsg({ k: "err", t: "Arrival time must be a number, or leave it empty." });
    if (heap.length >= 31) return setMsg({ k: "err", t: "The queue shows up to 31 tasks. Process some first." });
    setMsg({ k: "ok", t: `${name.trim()} (priority ${pv}) joins the queue.` });
    addTasks([[name.trim(), pv, at]]); setName("");
  };
  const sample = () => { if (heap.length + 3 > 31) return setMsg({ k: "err", t: "Clear the queue before loading the samples." }); setMsg(null); addTasks(SAMPLE_TASKS); };
  const next = () => {
    if (!heap.length) return setMsg({ k: "err", t: "The queue is empty. Add a task or load the sample tasks." });
    const top = heap[0], r = opExtract(heap, "min");
    setHeap(r.arr); p.load(r.steps); setDone((d) => [...d, top]);
    setMsg({ k: "ok", t: `Processing ${top.label} (priority ${top.v}).` });
    bump({ ops: 1, cmps: r.st.c, swaps: r.st.s, explore: "Extract Min" }); setOp({ name: "Process next", busy: true });
  };
  const remove = () => {
    if (!heap.length) return setMsg({ k: "err", t: "There is nothing to remove. The queue is empty." });
    const idx = heap.findIndex((x) => String(x.id) === rm);
    if (idx < 0) return setMsg({ k: "err", t: "Pick a task from the list to remove." });
    const t = heap[idx], r = opDeleteAt(heap, "min", idx);
    setHeap(r.arr); p.load(r.steps); setRm(""); setMsg({ k: "ok", t: `Removed ${t.label} without processing it.` });
    bump({ ops: 1, cmps: r.st.c, swaps: r.st.s, explore: "Delete" });
  };
  const clear = () => { setHeap([]); setDone([]); p.load([]); setMsg({ k: "info", t: "Queue cleared." }); setTick(1); };
  const top = heap[0];
  return (
    <div>
      <PageHead title="Priority Queue Command Center" sub="A min-heap on priority decides what runs next. Lower number = more urgent; ties go to the earlier arrival." />
      <Card>
        <div className="flex flex-wrap gap-2 items-center">
          <input className="inp flex-1" style={{ minWidth: 160 }} placeholder="Task name" value={name} onChange={(e) => setName(e.target.value)} onKeyDown={(e) => e.key === "Enter" && add()} aria-label="Task name" />
          <label className="text-sm mu" htmlFor="pq-p">Priority</label><input id="pq-p" className="inp" style={{ width: 70 }} value={pri} onChange={(e) => setPri(e.target.value)} inputMode="numeric" />
          <label className="text-sm mu" htmlFor="pq-a">Arrival</label><input id="pq-a" className="inp" style={{ width: 80 }} value={arr} placeholder={`T${tick}`} onChange={(e) => setArr(e.target.value)} inputMode="numeric" />
          <button className="btn btn-p" onClick={add}><Plus size={14} />Add task</button>
        </div>
        <div className="flex flex-wrap gap-2 items-center mt-3">
          <button className="btn btn-c" onClick={next}><Play size={14} />Process next</button>
          <select className="inp" value={rm} onChange={(e) => setRm(e.target.value)} aria-label="Task to remove"><option value="">Choose a task…</option>{heap.map((x) => <option key={x.id} value={x.id}>{x.label} (P{x.v})</option>)}</select>
          <button className="btn" onClick={remove}><Trash2 size={14} />Remove task</button>
          <button className="btn btn-d" onClick={clear}>Clear queue</button>
          <button className="btn" onClick={sample}><Sparkles size={14} />Load sample tasks</button>
        </div>
        <Msg m={msg} />
      </Card>
      <div className="grid md:grid-cols-4 gap-3 mt-4">
        <Card title="Incoming" icon={Plus}><p className="text-sm">{incoming || <span className="mu">No new arrivals</span>}</p></Card>
        <Card title="Priority heap" icon={Network}><p className="text-sm">{heap.length} task{heap.length === 1 ? "" : "s"} waiting</p></Card>
        <Card title="Next task" icon={ChevronRight}>{top ? <p className="text-sm"><b>{top.label}</b> <span className="mono tcy">P{top.v}</span></p> : <p className="mu text-sm">—</p>}</Card>
        <Card title="Processed" icon={Check}><p className="text-sm">{done.length ? `${done.length} done` : <span className="mu">None yet</span>}</p></Card>
      </div>
      <div className="grid xl:grid-cols-3 gap-4 mt-4">
        <Card className="xl:col-span-2" title="Heap view" icon={Network}>
          <TreeView arr={view} size={step ? step.size : heap.length} marks={step ? step.marks : {}} showLabel type="min" empty="The queue is empty. Add a task or load the sample tasks to see the heap." />
          <div className="mt-2"><ArrayView arr={view} size={step ? step.size : heap.length} marks={step ? step.marks : {}} /></div>
          <div className="mt-3"><Controls p={p} /></div>
        </Card>
        <div className="space-y-4">
          <OpPanel step={step} />
          <Card title="Processed order" icon={Check}>
            {done.length ? <ol className="text-sm space-y-1">{done.map((d, k) => <li key={k}><span className="mono mu">{k + 1}.</span> {d.label} <span className="mono mu">P{d.v}</span></li>)}</ol> : <p className="mu text-sm">Processed tasks appear here in the order they ran.</p>}
          </Card>
          <Mentor step={step} idle="Add tasks: each one is inserted into the heap, and the most urgent always rises to the root." />
        </div>
      </div>
    </div>
  );
}

/* ============================ PSEUDOCODE + ALGORITHM EXPLORER ============================ */
const dn = (m) => [
  "heapifyDown(i):", "  l = left(i);  r = right(i)", "  if l >= n: return                  // leaf",
  `  c = (r < n and A[r] ${m ? "<" : ">"} A[l]) ? r : l`, `  if A[c] ${m ? "<" : ">"} A[i]:`, "    swap(A[i], A[c])", "    heapifyDown(c)",
];
const upb = (m) => ["heapifyUp(i):", `  while i > 0 and A[i] ${m ? "<" : ">"} A[parent(i)]:`, "    swap(A[i], A[parent(i)])", "    i = parent(i)"];
const PC = {
  insert: (m) => ({ main: ["insert(x):", "  A[n] = x;  n = n + 1", "  i = n - 1", `  while i > 0 and A[parent(i)] ${m ? ">" : "<"} A[i]:`, "    swap(A[i], A[parent(i)])", "    i = parent(i)"] }),
  delete: (m) => ({ main: ["delete(i):", "  A[i] = A[n-1];  n = n - 1", `  if i > 0 and A[i] ${m ? "<" : ">"} A[parent(i)]:`, "    heapifyUp(i)", "  else:", "    heapifyDown(i)"], subs: { up: upb(m), down: dn(m) } }),
  extract: (m) => ({ main: [`extract${m ? "Min" : "Max"}():`, "  if n == 0: return ERROR", "  root = A[0]", "  A[0] = A[n-1];  n = n - 1", "  heapifyDown(0)", "  return root"], subs: { down: dn(m) } }),
  heapify: (m) => ({ main: dn(m) }),
  build: (m) => ({ main: ["buildHeap(A):", "  for i = floor(n/2) - 1 down to 0:", "    heapifyDown(i)"], subs: { down: dn(m) } }),
  sort: () => ({ main: ["heapSort(A):", "  buildMaxHeap(A)", "  for end = n-1 down to 1:", "    swap(A[0], A[end])", "    n = end", "    heapifyDown(0)"], subs: { down: dn(false) } }),
};
const ALGOS = {
  insert: { name: "Insert", pc: "insert", purpose: "Add a new element while keeping the tree complete and ordered.", input: "A heap A of size n and a value x.", output: "A heap of size n + 1 containing x.", steps: ["Place x at the end of the array.", "Compare x with its parent.", "If the heap property is violated, swap them.", "Repeat from the parent's position until no swap is needed or the root is reached."], time: "O(log n)", space: "O(1)" },
  delete: { name: "Delete", pc: "delete", purpose: "Remove the element at a given index.", input: "A heap A and an index i.", output: "A heap of size n - 1 without the old A[i].", steps: ["Overwrite A[i] with the last element and shrink the array.", "If the moved element beats its parent, sift it up.", "Otherwise sift it down.", "The heap property is restored."], time: "O(log n)", space: "O(1)" },
  extractMin: { name: "Extract Min", pc: "extract", type: "min", purpose: "Remove and return the smallest element of a min-heap.", input: "A non-empty min-heap A.", output: "The minimum, and a smaller min-heap.", steps: ["Save the root A[0].", "Move the last element to the root and shrink the array.", "Sink the new root with heapifyDown.", "Return the saved value."], time: "O(log n)", space: "O(1)" },
  extractMax: { name: "Extract Max", pc: "extract", type: "max", purpose: "Remove and return the largest element of a max-heap.", input: "A non-empty max-heap A.", output: "The maximum, and a smaller max-heap.", steps: ["Save the root A[0].", "Move the last element to the root and shrink the array.", "Sink the new root with heapifyDown.", "Return the saved value."], time: "O(log n)", space: "O(1)" },
  heapify: { name: "Heapify", pc: "heapify", purpose: "Fix one node whose subtrees are already heaps.", input: "An array A and an index i.", output: "The subtree rooted at i is a heap.", steps: ["Look at the children of i.", "Pick the better child.", "If it beats A[i], swap.", "Continue from the child's index."], time: "O(log n)", space: "O(1) iterative, O(log n) recursive" },
  build: { name: "Build Heap", pc: "build", purpose: "Turn an arbitrary array into a heap in place.", input: "Any array A of n elements.", output: "A, rearranged into a heap.", steps: ["Start at the last non-leaf node, floor(n/2) - 1.", "Run heapifyDown on it.", "Move one index toward the root and repeat.", "After index 0, the whole array is a heap."], time: "O(n)", space: "O(1)" },
  sort: { name: "Heap Sort", pc: "sort", type: "max", purpose: "Sort an array using a max-heap, in place.", input: "Any array A of n elements.", output: "A in ascending order.", steps: ["Build a max-heap.", "Swap the root with the last heap element.", "Shrink the heap by one.", "heapifyDown the new root; repeat until the heap is empty."], time: "O(n log n)", space: "O(1)" },
};
function AlgoPage() {
  const { bump, setOp } = useCtx();
  const [key, setKey] = useState("insert");
  const [type, setType] = useState("min");
  const [txt, setTxt] = useState("5, 9, 7, 12, 11, 8, 15");
  const [x, setX] = useState("3");
  const [base, setBase] = useState([]);
  const [msg, setMsg] = useState(null);
  const p = usePlayer();
  const A = ALGOS[key];
  const eff = A.type || type;
  const needsHeap = ["insert", "delete", "extractMin", "extractMax"].includes(key);
  const pc = PC[A.pc](eff === "min");
  useEffect(() => { setOp((o) => ({ ...o, busy: p.playing })); }, [p.playing]);
  const run = () => {
    const { vals, bad } = parseVals(txt);
    if (!vals.length) return setMsg({ k: "err", t: "No elements available. Enter a sample array first." });
    if (bad.length) return setMsg({ k: "err", t: `"${bad[0]}" is not a number.` });
    if (vals.length > 31) return setMsg({ k: "err", t: "Use at most 31 values." });
    const xv = Number(x);
    if ((key === "insert" || key === "delete" || key === "heapify") && !Number.isFinite(xv)) return setMsg({ k: "err", t: key === "insert" ? "x must be a number." : "The index must be a number." });
    setMsg(null);
    const items = needsHeap ? buildNow(vals, eff) : mk(vals);
    let r;
    if (key === "insert") r = opInsert(items, eff, { id: uid(), v: xv });
    else if (key === "delete") { const i = Math.round(xv); if (i < 0 || i >= items.length) return setMsg({ k: "err", t: `Index must be between 0 and ${items.length - 1}.` }); r = opDeleteAt(items, eff, i); }
    else if (key === "extractMin" || key === "extractMax") r = opExtract(items, eff);
    else if (key === "heapify") { const i = Math.round(xv); if (i < 0 || i >= items.length) return setMsg({ k: "err", t: `Index must be between 0 and ${items.length - 1}.` }); r = opHeapifyAt(items, eff, i); }
    else if (key === "build") r = opBuild(items, eff);
    else r = opSort(items, "asc");
    setBase(items); p.load(r.steps); setOp({ name: A.name, busy: true });
    bump({ ops: 1, cmps: r.st.c, swaps: r.st.s, processed: vals.length, explore: A.name });
  };
  const step = p.step;
  return (
    <div>
      <PageHead title="Algorithm Explorer" sub="Pick an algorithm, run it on your own data and watch the pseudocode line that is executing." />
      <div className="flex flex-wrap gap-2 mb-4">
        {Object.entries(ALGOS).map(([k, a]) => <button key={k} className={`btn ${key === k ? "btn-p" : ""}`} onClick={() => { setKey(k); p.load([]); setBase([]); setMsg(null); if (k === "delete" || k === "heapify") setX("1"); if (k === "insert") setX("3"); }}>{a.name}</button>)}
      </div>
      <div className="grid xl:grid-cols-3 gap-4">
        <div className="space-y-4">
          <Card title={A.name} icon={Compass}>
            <dl className="text-sm space-y-2.5">
              <div><dt className="mu text-xs">Purpose</dt><dd>{A.purpose}</dd></div>
              <div><dt className="mu text-xs">Input</dt><dd>{A.input}</dd></div>
              <div><dt className="mu text-xs">Output</dt><dd>{A.output}</dd></div>
              <div><dt className="mu text-xs">Algorithm steps</dt><dd><ol className="list-decimal pl-5 space-y-1">{A.steps.map((s) => <li key={s}>{s}</li>)}</ol></dd></div>
              <div className="grid grid-cols-2 gap-3"><div><dt className="mu text-xs">Time complexity</dt><dd className="mono tcy font-bold">{A.time}</dd></div><div><dt className="mu text-xs">Space complexity</dt><dd className="mono">{A.space}</dd></div></div>
            </dl>
          </Card>
          <Card title="Pseudocode" icon={Code2}><PseudoCode pc={pc} step={step} /></Card>
        </div>
        <div className="xl:col-span-2 space-y-4">
          <Card>
            <div className="flex flex-wrap gap-2 items-center">
              {!A.type && <TypeSeg value={type} onChange={(t) => { setType(t); p.load([]); }} />}
              <input className="inp flex-1" style={{ minWidth: 180 }} value={txt} onChange={(e) => setTxt(e.target.value)} aria-label="Sample data" />
              {(key === "insert" || key === "delete" || key === "heapify") && <><label className="text-sm mu" htmlFor="alx">{key === "insert" ? "x =" : "index ="}</label><input id="alx" className="inp" style={{ width: 70 }} value={x} onChange={(e) => setX(e.target.value)} /></>}
              <button className="btn btn-p" onClick={run}><Play size={14} />Run on this data</button>
            </div>
            {needsHeap && <p className="text-xs mu mt-2">The sample data is first built into a valid {eff}-heap, then {A.name.toLowerCase()} runs on it.</p>}
            <Msg m={msg} />
          </Card>
          <Card title="Visualization" icon={Network}>
            {!p.total ? <p className="mu text-sm py-6 text-center">Press “Run on this data” to see the steps and the highlighted pseudocode.</p> : <VizBlock p={p} base={base} type={eff} />}
          </Card>
          <div className="grid md:grid-cols-2 gap-4"><OpPanel step={step} /><Mentor step={step} /></div>
        </div>
      </div>
    </div>
  );
}

/* ============================ COMPLEXITY ============================ */
const CX = [
  ["Insert", "O(1)", "O(1)*", "O(log n)"], ["Delete", "O(1)", "O(log n)", "O(log n)"], ["Extract", "O(1)", "O(log n)", "O(log n)"],
  ["Peek", "O(1)", "O(1)", "O(1)"], ["Heapify", "O(1)", "O(log n)", "O(log n)"], ["Build heap", "O(n)", "O(n)", "O(n)"], ["Heap sort", "O(n log n)", "O(n log n)", "O(n log n)"],
];
const NS = [10, 50, 100, 500, 1000];
const est = (n) => ({ n, Peek: 1, Insert: Math.ceil(Math.log2(n + 1)), "Extract / Delete": Math.max(1, 2 * Math.floor(Math.log2(n))), "Build heap": 2 * n, "Heap sort": Math.round(n * Math.log2(n)) });
function ComplexityPage() {
  const [n, setN] = useState(100);
  const [m, setM] = useState(null);
  const e = est(n);
  const data = NS.map(est);
  const lines = [["Peek", "#34d399"], ["Insert", "#22d3ee"], ["Extract / Delete", "#60a5fa"], ["Build heap", "#a78bfa"], ["Heap sort", "#f472b6"]];
  const measureIt = () => { const vals = Array.from({ length: n }, () => rndInt(1, 100000)); setM({ n, ...measure(vals) }); };
  return (
    <div>
      <PageHead title="Complexity Lab" sub="See how the number of operations grows with input size." />
      <Card className="overflow-x-auto" title="Operation costs" icon={Activity}>
        <table><thead><tr><th>Operation</th><th>Best</th><th>Average</th><th>Worst</th></tr></thead>
          <tbody>{CX.map(([a, b, c, d]) => <tr key={a}><td className="font-semibold">{a}</td><td className="mono">{b}</td><td className="mono">{c}</td><td className="mono tcy">{d}</td></tr>)}</tbody></table>
        <p className="text-xs mu mt-2">* Inserting random values moves up only a constant number of levels on average. The guaranteed bound is O(log n).</p>
      </Card>
      <Card className="mt-4" title="Input size vs operation count" icon={Activity} right={<Seg value={n} onChange={setN} options={NS.map((v) => [v, String(v)])} />}>
        <div style={{ width: "100%", height: 300 }}>
          <ResponsiveContainer>
            <LineChart data={data} margin={{ top: 8, right: 16, left: 0, bottom: 0 }}>
              <CartesianGrid stroke="rgba(150,160,210,.2)" strokeDasharray="3 4" />
              <XAxis dataKey="n" stroke="#8f98c4" tick={{ fontSize: 12 }} label={{ value: "n", position: "insideBottomRight", offset: -4, fill: "#8f98c4" }} />
              <YAxis scale="log" domain={[1, "auto"]} allowDataOverflow stroke="#8f98c4" tick={{ fontSize: 12 }} width={56} />
              <RTooltip contentStyle={{ background: "#12163a", border: "1px solid #2c3270", borderRadius: 10, color: "#eef1ff" }} />
              <RLegend />
              {lines.map(([k, c]) => <Line key={k} type="monotone" dataKey={k} stroke={c} strokeWidth={2.4} dot={{ r: 3 }} />)}
            </LineChart>
          </ResponsiveContainer>
        </div>
        <p className="text-xs mu">Estimated operations (log scale). Insert ≈ log₂(n+1) swaps at most; extract ≈ 2·log₂ n comparisons; build ≈ 2n comparisons; heap sort ≈ n·log₂ n.</p>
        <div className="grid grid-cols-2 sm:grid-cols-5 gap-2 mt-3">
          {lines.map(([k]) => <div key={k} className="rounded-lg p-2" style={{ background: "var(--panel2)" }}><div className="text-xs mu">{k} at n = {n}</div><div className="mono font-bold">{e[k].toLocaleString()}</div></div>)}
        </div>
      </Card>
      <Card className="mt-4" title="Measured on real random data" icon={FlaskConical} right={<button className="btn btn-p" onClick={measureIt}><Play size={14} />Measure n = {n}</button>}>
        {!m ? <p className="mu text-sm">Press the button: HEAPVERSE runs the real algorithms on {n} random numbers and counts every comparison and swap.</p> : (
          <table><thead><tr><th>Algorithm (n = {m.n})</th><th>Comparisons</th><th>Swaps</th></tr></thead>
            <tbody>
              <tr><td>Build heap (bottom-up)</td><td className="mono">{m.build.c}</td><td className="mono">{m.build.s}</td></tr>
              <tr><td>{m.n} inserts (one by one)</td><td className="mono">{m.insert.c}</td><td className="mono">{m.insert.s}</td></tr>
              <tr><td>Heap sort</td><td className="mono">{m.sort.c}</td><td className="mono">{m.sort.s}</td></tr>
            </tbody></table>
        )}
      </Card>
    </div>
  );
}

/* ============================ CHALLENGE ARENA ============================ */
const shuffle = (a) => { const b = a.slice(); for (let i = b.length - 1; i > 0; i--) { const j = rndInt(0, i); [b[i], b[j]] = [b[j], b[i]]; } return b; };
const optsOf = (c, cands, k = 4) => { const s = new Set([c]); for (const x of shuffle(cands)) { if (s.size >= k) break; s.add(x); } let t = 1; while (s.size < k) s.add(c + t++); return shuffle([...s]); };
const distinct = (n, lo = 1, hi = 60) => { const s = new Set(); while (s.size < n) s.add(rndInt(lo, hi)); return [...s]; };
const LEVELS = ["Heap Explorer", "Heap Builder", "Heap Master", "Algorithm Architect"];
const PTS = [10, 15, 20, 30];
const GENS = [
  { lv: 1, f: () => { const t = Math.random() < 0.5 ? "min" : "max", v = distinct(6); const a = t === "min" ? Math.min(...v) : Math.max(...v);
    return { kind: "mc", type: t, raw: mk(v), text: `These values are inserted into an empty ${t}-heap. Which element ends up as the root?`, options: optsOf(a, v), answer: a, why: `A ${t}-heap keeps the ${t === "min" ? "smallest" : "largest"} value at index 0, so the root is ${a}.` }; } },
  { lv: 1, f: () => { const i = rndInt(3, 14); const a = (i - 1) >> 1;
    return { kind: "mc", text: `Using zero-based indexing, what is the parent index of index ${i}?`, options: optsOf(a, [i >> 1, a + 1, a - 1, i - 2, (i + 1) >> 1].filter((x) => x >= 0)), answer: a, why: `Parent = floor((i - 1) / 2) = floor(${i - 1} / 2) = ${a}.` }; } },
  { lv: 1, f: () => { const i = rndInt(1, 7), right = Math.random() < 0.5, a = 2 * i + (right ? 2 : 1);
    return { kind: "mc", text: `Using zero-based indexing, what is the ${right ? "right" : "left"} child index of index ${i}?`, options: optsOf(a, [2 * i, 2 * i + 1, 2 * i + 2, 2 * i + 3, i + 1].filter((x) => x !== a)), answer: a, why: `${right ? "Right" : "Left"} child = 2i + ${right ? 2 : 1} = ${a}.` }; } },
  { lv: 2, f: () => { const t = Math.random() < 0.5 ? "min" : "max"; let h = buildNow(distinct(7), t);
    if (Math.random() < 0.5) { const c = h.slice(); const i = rndInt(3, 6), p = parentOf(i); [c[i], c[p]] = [c[p], c[i]]; h = c; }
    const bad = validate(h, t), ok = bad.length === 0;
    return { kind: "mc", type: t, show: h, text: `Is this array a valid ${t}-heap?`, options: ["Yes, valid", "No, invalid"], answer: ok ? "Yes, valid" : "No, invalid", why: ok ? `Every parent is ${t === "min" ? "≤" : "≥"} both children.` : bad[0].msg }; } },
  { lv: 2, f: () => { const t = Math.random() < 0.5 ? "min" : "max"; const vals = distinct(6, 10, 60), h = buildNow(vals, t); let v; do v = rndInt(1, 70); while (vals.includes(v));
    const par = h[parentOf(h.length)], swaps = lt(t, { v }, par); const a = swaps ? par.v : "No swap";
    return { kind: "mc", type: t, show: h, text: `Insert ${v} into this ${t}-heap. Which value does ${v} swap with first?`, options: optsOf(a, [...vals, "No swap"]), answer: a, why: swaps ? `${v} lands at index ${h.length}; its parent is ${par.v}, and ${v} ${t === "min" ? "<" : ">"} ${par.v}, so they swap first.` : `${v} lands under ${par.v} and already respects the ${t}-heap order, so there is no swap.` }; } },
  { lv: 3, f: () => { const t = Math.random() < 0.5 ? "min" : "max"; const h = buildNow(distinct(7), t); const r = opExtract(h, t); const a = r.arr[0].v;
    return { kind: "mc", type: t, show: h, text: `Extract the ${t === "min" ? "minimum" : "maximum"} once. What is the new root?`, options: optsOf(a, h.map((x) => x.v)), answer: a, why: `${h[0].v} leaves. The last element moves to the root and sinks; the better of the old root's two children rises, giving ${a}.` }; } },
  { lv: 3, f: () => { const t = Math.random() < 0.5 ? "min" : "max"; const vals = distinct(7, 10, 60), h = buildNow(vals, t); const v = t === "min" ? rndInt(1, 9) : rndInt(61, 99); const a = opInsert(h, t, { id: uid(), v }).st.s;
    return { kind: "mc", type: t, show: h, text: `How many swaps does inserting ${v} into this ${t}-heap take?`, options: optsOf(a, [0, 1, 2, 3, 4]), answer: a, why: `${v} is ${t === "min" ? "smaller" : "larger"} than everything, so it climbs until it reaches the root: ${a} swaps.` }; } },
  { lv: 4, f: () => { const t = Math.random() < 0.5 ? "min" : "max"; let v, a; do { v = distinct(7); a = opBuild(mk(v), t).st.s; } while (a === 0);
    return { kind: "mc", type: t, raw: mk(v), text: `How many swaps does Build Heap make to turn this array into a ${t}-heap?`, options: optsOf(a, [1, 2, 3, 4, 5]), answer: a, why: `Running bottom-up heapify from index 2 down to 0 performs ${a} swaps.` }; } },
  { lv: 4, f: () => { const t = Math.random() < 0.5 ? "min" : "max"; let v; do v = mk(distinct(6)); while (validate(v, t).length === 0);
    return { kind: "drag", type: t, items: v, text: `Rearrange the array into a valid ${t}-heap. Drag cells onto each other (or tap two cells) to swap them.`, why: `Any arrangement where every parent is ${t === "min" ? "≤" : "≥"} its children works. Build Heap would do it in ${opBuild(v, t).st.s} swaps.` }; } },
];
function SwapArray({ items, onChange, type, disabled }) {
  const [dg, setDg] = useState(null), [pick, setPick] = useState(null);
  const bad = new Set(validate(items, type).flatMap((v) => [v.p, v.c]));
  const swap = (a, b) => { if (a == null || a === b || disabled) return; const c = items.slice(); [c[a], c[b]] = [c[b], c[a]]; onChange(c); };
  return (
    <div className="flex flex-wrap gap-2">
      {items.map((it, i) => (
        <div key={it.id} draggable={!disabled} onDragStart={() => setDg(i)} onDragOver={(e) => e.preventDefault()} onDrop={() => { swap(dg, i); setDg(null); }}
          onClick={() => { if (disabled) return; if (pick == null) setPick(i); else { swap(pick, i); setPick(null); } }} role="button" tabIndex={0}
          onKeyDown={(e) => { if (e.key === "Enter") { if (pick == null) setPick(i); else { swap(pick, i); setPick(null); } } }} aria-label={`Cell ${i}, value ${it.v}`}
          style={{ cursor: disabled ? "default" : "grab", width: 52 }}>
          <div className="mono font-bold flex items-center justify-center" style={{ height: 46, borderRadius: 10, border: `2px solid ${pick === i ? "var(--cy)" : bad.has(i) ? "var(--rem)" : "var(--ns)"}`, background: "var(--node)" }}>{it.v}</div>
          <div className="mono text-center mu" style={{ fontSize: 11, marginTop: 2 }}>{i}</div>
        </div>
      ))}
    </div>
  );
}
function ChallengePage() {
  const { bump } = useCtx();
  const R = 10;
  const [g, setG] = useState({ k: 0, score: 0, ok: 0, streak: 0, best: 0, over: false });
  const [q, setQ] = useState(null);
  const [ans, setAns] = useState(null);
  const [items, setItems] = useState([]);
  const level = Math.min(3, Math.floor(g.ok / 3));
  const make = (lv) => { const pool = GENS.filter((x) => x.lv <= lv + 1), top = pool.filter((x) => x.lv === lv + 1); const pick = (Math.random() < 0.6 && top.length ? top : pool); const nq = pick[rndInt(0, pick.length - 1)].f(); setQ(nq); setAns(null); setItems(nq.items || []); };
  useEffect(() => { make(0); }, []);
  const settle = (good, lv) => {
    setAns({ good });
    setG((s) => { const streak = good ? s.streak + 1 : 0; const gain = good ? PTS[lv] + (streak >= 3 ? 5 : 0) : 0; return { ...s, score: s.score + gain, ok: s.ok + (good ? 1 : 0), streak, best: Math.max(s.best, streak) }; });
    bump({ done: good ? 1 : 0, total: 1 });
  };
  const pickOpt = (o) => { if (ans) return; settle(o === q.answer, level); };
  const check = () => { if (ans) return; settle(validate(items, q.type).length === 0, level); };
  const next = () => {
    if (g.k + 1 >= R) { setG((s) => ({ ...s, over: true })); bump({ score: g.score }); return; }
    setG((s) => ({ ...s, k: s.k + 1 })); make(level);
  };
  const again = () => { setG({ k: 0, score: 0, ok: 0, streak: 0, best: 0, over: false }); make(0); };
  const acc = g.k + (ans ? 1 : 0) ? Math.round((100 * g.ok) / (g.k + (ans ? 1 : 0))) : 0;
  if (g.over) {
    const fl = Math.min(3, Math.floor(g.ok / 3));
    return (
      <div>
        <PageHead title="Heap Challenge Arena" />
        <Card className="text-center py-8">
          <p className="mu text-sm">Heap mastery score</p>
          <p className="text-6xl font-bold mono tcy my-2">{g.score}</p>
          <p className="font-semibold">{LEVELS[fl]}</p>
          <p className="mu text-sm mt-2">{g.ok} of {R} correct · accuracy {Math.round((100 * g.ok) / R)}% · best streak {g.best}</p>
          <button className="btn btn-p mt-5" onClick={again}><RotateCcw size={14} />Play another round</button>
        </Card>
      </div>
    );
  }
  return (
    <div>
      <PageHead title="Heap Challenge Arena" sub={`Question ${g.k + 1} of ${R}. Higher levels unlock as you answer correctly.`} />
      <div className="grid grid-cols-2 md:grid-cols-4 gap-3 mb-4">
        <Tile label="Score" value={g.score} tone="tcy" /><Tile label="Accuracy" value={`${acc}%`} /><Tile label="Streak" value={g.streak} />
        <Tile label="Level" value={`${level + 1} · ${LEVELS[level]}`} />
      </div>
      {q && (
        <Card>
          <p className="font-semibold mb-3">{q.text}</p>
          {q.raw && <div className="mb-3"><ArrayView arr={q.raw} rootGlow={false} /></div>}
          {q.show && <div className="mb-3"><TreeView arr={q.show} type={q.type} rootGlow={false} /><ArrayView arr={q.show} /></div>}
          {q.kind === "mc" && (
            <div className="grid grid-cols-2 gap-2 max-w-md">
              {q.options.map((o) => {
                const right = ans && o === q.answer, wrong = ans && !ans.good && false;
                return <button key={String(o)} className={`btn ${right ? "btn-c" : ""}`} disabled={!!ans && !right} onClick={() => pickOpt(o)}>{String(o)}</button>;
              })}
            </div>
          )}
          {q.kind === "drag" && (
            <div className="space-y-3">
              <TreeView arr={items} type={q.type} showProp rootGlow={false} />
              <SwapArray items={items} onChange={setItems} type={q.type} disabled={!!ans} />
              <button className="btn btn-p" disabled={!!ans} onClick={check}><Check size={14} />Check my heap</button>
            </div>
          )}
          {ans && (
            <div className="mt-4">
              <p className={`font-semibold ${ans.good ? "tgr" : "tre"}`}>{ans.good ? "✓ Correct" : "✕ Not quite"}</p>
              <p className="text-sm mu mt-1">{q.why}</p>
              <button className="btn btn-p mt-3" onClick={next}>{g.k + 1 >= R ? "See my score" : "Next question"}<ChevronRight size={14} /></button>
            </div>
          )}
        </Card>
      )}
    </div>
  );
}

/* ============================ VALIDATE & REPAIR ============================ */
function ValidatorPanel() {
  const { bump } = useCtx();
  const [txt, setTxt] = useState("1, 4, 2, 10, 8, 15");
  const [type, setType] = useState("min");
  const [r, setR] = useState(null);
  const [msg, setMsg] = useState(null);
  const check = (t = type, s = txt) => {
    const { vals, bad } = parseVals(s);
    if (!vals.length) return setMsg({ k: "err", t: "No elements available. Enter an array such as 1, 4, 2, 10, 8, 15." });
    if (bad.length) return setMsg({ k: "err", t: `"${bad[0]}" is not a number.` });
    if (vals.length > 31) return setMsg({ k: "err", t: "Use at most 31 values." });
    setMsg(null);
    const items = mk(vals), viol = validate(items, t);
    setR({ items, viol, t }); bump({ ops: 1, explore: undefined });
  };
  const marks = r ? { bad: [...new Set(r.viol.flatMap((v) => [v.p, v.c]))] } : {};
  return (
    <div className="space-y-4">
      <Card>
        <div className="flex flex-wrap gap-2 items-center">
          <TypeSeg value={type} onChange={(t) => { setType(t); if (r) check(t); }} />
          <input className="inp flex-1" style={{ minWidth: 200 }} value={txt} onChange={(e) => setTxt(e.target.value)} onKeyDown={(e) => e.key === "Enter" && check()} aria-label="Array to check" />
          <button className="btn btn-p" onClick={() => check()}><ShieldCheck size={14} />Check heap</button>
          <button className="btn" onClick={() => { setTxt("1, 4, 2, 3, 8, 0"); setType("min"); check("min", "1, 4, 2, 3, 8, 0"); }}>Load invalid example</button>
        </div>
        <Msg m={msg} />
      </Card>
      {r && (
        <Card title="Result" icon={ShieldCheck}>
          <p className="text-xl font-bold" style={{ color: r.viol.length ? "var(--rem)" : "var(--new)" }}>{r.viol.length ? "✕ Not a valid heap" : `✓ Valid ${r.t} heap`}</p>
          {r.viol.length > 0 && <ul className="text-sm mt-2 space-y-1">{r.viol.map((v, k) => <li key={k} className="mono">{v.msg}</li>)}</ul>}
          <TreeView arr={r.items} marks={marks} type={r.t} showProp rootGlow={false} />
          <ArrayView arr={r.items} marks={marks} />
        </Card>
      )}
    </div>
  );
}
function RepairPanel() {
  const { bump } = useCtx();
  const [txt, setTxt] = useState("1, 4, 2, 3, 8, 0");
  const [type, setType] = useState("min");
  const [items, setItems] = useState(() => mk([1, 4, 2, 3, 8, 0]));
  const [orig, setOrig] = useState(items);
  const [mode, setMode] = useState("manual");
  const [moves, setMoves] = useState(0);
  const [sel, setSel] = useState(null);
  const [hint, setHint] = useState(null);
  const [msg, setMsg] = useState(null);
  const p = usePlayer();
  const step = p.step;
  const arr = step ? step.arr : items;
  const viol = validate(arr, type, step ? step.size : arr.length);
  const optimal = opBuild(orig, type).st.s;
  const load = () => {
    const { vals, bad } = parseVals(txt);
    if (!vals.length) return setMsg({ k: "err", t: "No elements available. Enter an array to repair." });
    if (bad.length) return setMsg({ k: "err", t: `"${bad[0]}" is not a number.` });
    if (vals.length > 31) return setMsg({ k: "err", t: "Use at most 31 values." });
    const it = mk(vals); setItems(it); setOrig(it); setMoves(0); setSel(null); setHint(null); p.load([]);
    setMsg(validate(it, type).length ? { k: "info", t: "This array breaks the heap property. Find the violation." } : { k: "ok", t: "This array is already a valid heap. Enter an invalid one to practice." });
  };
  const auto = () => { const r = opBuild(items, type); setItems(r.arr); p.load(r.steps); setSel(null); setHint(null); bump({ ops: 1, cmps: r.st.c, swaps: r.st.s, explore: "Build Heap" }); };
  const click = (i) => {
    if (mode !== "manual" || step) return;
    if (sel == null) return setSel(i);
    if (sel === i) return setSel(null);
    const c = items.slice(); [c[sel], c[i]] = [c[i], c[sel]]; setItems(c); setMoves((m) => m + 1); setSel(null); setHint(null);
    if (validate(c, type).length === 0) { bump({ ops: 1, swaps: moves + 1 }); setMsg({ k: "ok", t: `Repaired in ${moves + 1} swap${moves ? "s" : ""}. The Build Heap algorithm needs ${optimal}.` }); }
  };
  const marks = { bad: [...new Set(viol.flatMap((v) => [v.p, v.c]))], ...(step ? step.marks : {}) };
  const rings = hint ? { [hint.p]: "var(--vi)", [hint.c]: "var(--cy)" } : {};
  return (
    <div className="space-y-4">
      <Card>
        <div className="flex flex-wrap gap-2 items-center">
          <TypeSeg value={type} onChange={(t) => { setType(t); setMsg(null); }} />
          <input className="inp flex-1" style={{ minWidth: 200 }} value={txt} onChange={(e) => setTxt(e.target.value)} onKeyDown={(e) => e.key === "Enter" && load()} aria-label="Broken heap" />
          <button className="btn btn-p" onClick={load}><Hammer size={14} />Repair this heap</button>
        </div>
        <div className="flex flex-wrap gap-2 items-center mt-3">
          <Seg value={mode} onChange={(m) => { setMode(m); setSel(null); }} options={[["manual", "Manual repair"], ["auto", "Auto repair"]]} />
          {mode === "auto" && <button className="btn btn-c" disabled={!viol.length || !!step} onClick={auto}><Wand2 size={14} />Run auto repair</button>}
          {mode === "manual" && <>
            <button className="btn" disabled={!viol.length} onClick={() => setHint(viol[viol.length - 1])}><Eye size={14} />Hint</button>
            <button className="btn" onClick={() => { setItems(orig); setMoves(0); setSel(null); setHint(null); setMsg(null); }}><RotateCcw size={14} />Start over</button>
            <span className="mono text-sm mu">Swaps: {moves}</span></>}
        </div>
        <Msg m={msg} />
      </Card>
      <div className="grid xl:grid-cols-3 gap-4">
        <Card className="xl:col-span-2" title={mode === "manual" ? "Click two nodes to swap them" : "Algorithm repair"} icon={Network}>
          <p className="text-sm mb-2" style={{ color: viol.length ? "var(--rem)" : "var(--new)" }}>{viol.length ? `⚠ ${viol.length} violation${viol.length > 1 ? "s" : ""} found` : "✓ Valid heap"}</p>
          <TreeView arr={arr} size={step ? step.size : arr.length} marks={marks} type={type} sel={sel} onSel={click} rings={rings} showProp rootGlow={false} />
          <div className="mt-2"><ArrayView arr={arr} size={step ? step.size : arr.length} marks={marks} sel={sel} onSel={click} rings={rings} /></div>
          {step && <div className="mt-3"><Controls p={p} /></div>}
        </Card>
        <div className="space-y-4">
          <Card title="Violations" icon={AlertTriangle}>
            {viol.length ? <ul className="text-xs mono space-y-1.5">{viol.map((v, k) => <li key={k}>{v.msg}</li>)}</ul> : <p className="text-sm tgr">None. Every parent respects its children.</p>}
          </Card>
          {step && <OpPanel step={step} />}
          {step && <Mentor step={step} />}
        </div>
      </div>
    </div>
  );
}
function RepairPage() {
  const [tab, setTab] = useState("validate");
  return (
    <div>
      <PageHead title={tab === "validate" ? "Is this a heap?" : "Repair this heap"} sub={tab === "validate" ? "Paste an array and find exactly where the heap property breaks." : "Fix an invalid heap yourself, or let the algorithm do it."}
        right={<Seg value={tab} onChange={setTab} options={[["validate", "Validator"], ["repair", "Repair mode"]]} />} />
      {tab === "validate" ? <ValidatorPanel /> : <RepairPanel />}
    </div>
  );
}

/* ============================ DRAG BUILDER ============================ */
function BuilderPage() {
  const { bump } = useCtx();
  const N0 = 6;
  const [type, setType] = useState("min");
  const [pool, setPool] = useState(() => mk([5, 10, 3, 20, 8, 15]));
  const [slots, setSlots] = useState(() => Array(N0).fill(null));
  const [drag, setDrag] = useState(null);
  const [pick, setPick] = useState(null);
  const [anim, setAnim] = useState(false);
  const p = usePlayer();
  const N = slots.length;
  const first = slots.findIndex((s) => !s);
  const complete = first === -1 || slots.slice(first).every((s) => !s);
  const viol = validate(slots, type);
  const placed = slots.filter(Boolean).length;
  const valid = complete && viol.length === 0 && placed === N;
  const move = (src, d) => {
    if (!src) return;
    const p2 = pool.slice(), s2 = slots.slice();
    const card = src.from === "pool" ? p2[src.i] : s2[src.i];
    if (!card) return;
    const ex = s2[d];
    if (src.from === "pool") { p2.splice(src.i, 1); if (ex) p2.push(ex); } else s2[src.i] = ex || null;
    s2[d] = card; setPool(p2); setSlots(s2); setPick(null); setDrag(null);
  };
  const toPool = (src) => {
    if (!src || src.from !== "slot" || !slots[src.i]) return;
    const s2 = slots.slice(), card = s2[src.i]; s2[src.i] = null; setSlots(s2); setPool([...pool, card]); setPick(null); setDrag(null);
  };
  const fresh = () => { const v = distinct(N0, 1, 30); setPool(mk(v)); setSlots(Array(N0).fill(null)); setPick(null); setAnim(false); p.load([]); };
  const fix = () => {
    const all = [...slots.filter(Boolean), ...pool];
    const r = opBuild(all, type);
    p.load(r.steps); setAnim(true); setPool([]); setSlots(r.arr.concat(Array(N - r.arr.length).fill(null)));
    bump({ ops: 1, cmps: r.st.c, swaps: r.st.s, explore: "Build Heap" });
  };
  const cell = (it, src, key, extra) => (
    <div key={key} draggable onDragStart={() => setDrag(src)} onClick={(e) => { e.stopPropagation(); setPick(pick && pick.from === src.from && pick.i === src.i ? null : src); }}
      className="mono font-bold flex items-center justify-center" role="button" tabIndex={0} aria-label={`Card ${it.v}`}
      style={{ width: 46, height: 46, borderRadius: 999, border: `2px solid ${pick && pick.from === src.from && pick.i === src.i ? "var(--cy)" : extra || "var(--ns)"}`, background: "var(--node)", cursor: "grab" }}>{it.v}</div>
  );
  const badIdx = new Set(viol.flatMap((v) => [v.p, v.c]));
  const rows = [];
  for (let d = 0; (1 << d) - 1 < N; d++) rows.push(Array.from({ length: Math.min(1 << d, N - ((1 << d) - 1)) }, (_, k) => (1 << d) - 1 + k));
  return (
    <div>
      <PageHead title="Drag-and-Drop Heap Builder" sub="Drag number cards into the tree (or tap a card, then tap a slot). The lab checks both heap properties live." />
      <Card>
        <div className="flex flex-wrap gap-2 items-center">
          <TypeSeg value={type} onChange={setType} />
          <button className="btn btn-c" onClick={fix}><Wand2 size={14} />Let the algorithm fix it</button>
          <button className="btn" onClick={fresh}><Shuffle size={14} />New cards</button>
          <button className="btn" onClick={() => { setPool(mk([5, 10, 3, 20, 8, 15])); setSlots(Array(N0).fill(null)); setAnim(false); p.load([]); }}><RotateCcw size={14} />Reset</button>
        </div>
      </Card>
      {anim ? (
        <Card className="mt-4" title="Build heap, step by step" icon={Network} right={<button className="btn" onClick={() => { setAnim(false); p.load([]); }}>Back to builder</button>}>
          <VizBlock p={p} base={slots.filter(Boolean)} type={type} />
          <p className="text-sm mt-2">{p.step ? p.step.m || p.step.title : ""}</p>
        </Card>
      ) : (
        <div className="grid lg:grid-cols-3 gap-4 mt-4">
          <Card className="lg:col-span-2" title="Your tree" icon={Network}>
            <div className="space-y-4 py-2">
              {rows.map((row, d) => (
                <div key={d} className="flex justify-around gap-2">
                  {row.map((i) => (
                    <div key={i} className="text-center" onDragOver={(e) => e.preventDefault()} onDrop={() => move(drag, i)} onClick={() => pick && move(pick, i)}>
                      {slots[i] ? cell(slots[i], { from: "slot", i }, "c" + i, badIdx.has(i) ? "var(--rem)" : "var(--new)") : (
                        <div style={{ width: 46, height: 46, borderRadius: 999, border: "2px dashed var(--line)", cursor: pick ? "pointer" : "default" }} aria-label={`Empty slot ${i}`} />
                      )}
                      <div className="mono mu" style={{ fontSize: 11, marginTop: 2 }}>{i}</div>
                    </div>
                  ))}
                </div>
              ))}
            </div>
            <div className="mt-3" onDragOver={(e) => e.preventDefault()} onDrop={() => toPool(drag)} onClick={() => pick && toPool(pick)}>
              <div className="text-xs mu mb-1">Number cards {pool.length === 0 ? "(all placed)" : "(drop a node here to take it back)"}</div>
              <div className="flex flex-wrap gap-2 min-h-[50px] p-2 rounded-xl" style={{ border: "1px dashed var(--line)" }}>{pool.map((it, i) => cell(it, { from: "pool", i }, it.id))}</div>
            </div>
          </Card>
          <div className="space-y-4">
            <Card title="Live check" icon={ShieldCheck}>
              <ul className="text-sm space-y-2">
                <li style={{ color: complete ? "var(--new)" : "var(--rem)" }}>{complete ? "✓ Valid structure" : "⚠ Not a complete tree: fill the slots from left to right with no gaps"}</li>
                <li style={{ color: viol.length ? "var(--rem)" : "var(--new)" }}>{viol.length ? "⚠ Invalid heap" : "✓ Heap property holds"}</li>
                {viol.slice(0, 3).map((v, k) => <li key={k} className="mono text-xs mu">{v.msg}</li>)}
                {valid && <li className="tgr font-semibold">✓ You built a valid {type}-heap!</li>}
                {!valid && placed < N && <li className="mu text-xs">{N - placed} card{N - placed > 1 ? "s" : ""} still to place.</li>}
              </ul>
            </Card>
            <Card title="Array so far" icon={Boxes}><ArrayView arr={slots.filter(Boolean)} rootGlow={false} /></Card>
          </div>
        </div>
      )}
    </div>
  );
}

/* ============================ APPLICATIONS ============================ */
const APPS = [
  { id: "er", name: "Emergency Room", type: "min", key: "Severity (1 = critical)", blurb: "Patients are treated by urgency, not arrival order.", items: [["Sprained ankle", 4], ["Chest pain", 1], ["Fever", 3]], incoming: [["Broken arm", 2], ["Mild cough", 5], ["Car accident", 1]], how: ["Each arriving patient is inserted with a severity score.", "The most critical patient is always at the root.", "Doctors call extractMin to take the next patient in O(log n)."] },
  { id: "cpu", name: "CPU Scheduling", type: "min", key: "Priority (1 = highest)", blurb: "The scheduler picks the next process to run.", items: [["Process A", 4], ["Process B", 1], ["Process C", 3]], incoming: [["Process D", 2], ["Process E", 5]], how: ["Ready processes sit in a priority heap.", "When the CPU frees up, the highest-priority process is extracted.", "New processes can arrive at any time and are inserted in O(log n)."] },
  { id: "net", name: "Network Routing", type: "min", key: "Traffic class (1 = urgent)", blurb: "Routers send time-critical packets first.", items: [["Bulk download", 5], ["Video call", 1], ["Web page", 3]], incoming: [["Voice packet", 1], ["Email", 4]], how: ["Queued packets are ordered by traffic class.", "Voice and video leave the router before bulk traffic.", "A heap keeps this ordering cheap even for thousands of packets."] },
  { id: "task", name: "Task Scheduling", type: "min", key: "Deadline (hours)", blurb: "Always work on the nearest deadline.", items: [["Submit report", 8], ["Fix bug", 2], ["Team sync", 5]], incoming: [["Production outage", 1], ["Plan sprint", 12]], how: ["Tasks are keyed by their deadline.", "extractMin returns the most urgent task.", "Adding a new task never requires re-sorting the whole list."] },
  { id: "event", name: "Event Simulation", type: "min", key: "Event time", blurb: "Simulators always process the earliest event.", items: [["Customer arrives", 5], ["Server finishes", 9], ["Door opens", 2]], incoming: [["Alarm rings", 3], ["Shift ends", 15]], how: ["Future events wait in a min-heap keyed by time.", "The simulator extracts the earliest event and advances the clock.", "Handling an event often schedules new events: more inserts."] },
  { id: "job", name: "Job Scheduling", type: "max", key: "Profit", blurb: "Pick the most profitable job first (a max-heap).", items: [["Job A", 20], ["Job B", 50], ["Job C", 35]], incoming: [["Job D", 60], ["Job E", 10]], how: ["A max-heap keeps the highest profit at the root.", "extractMax gives the best job available.", "The same idea powers top-K and greedy selection problems."] },
  { id: "dij", name: "Dijkstra's Algorithm", type: "min", key: "Tentative distance", blurb: "The closest unvisited vertex is always processed next.", items: [["A (start)", 0], ["B", 7], ["C", 9]], incoming: [["D via B", 11], ["C via B (better)", 8]], how: ["Vertices are stored with their best known distance.", "extractMin gives the closest unvisited vertex.", "When an edge improves a distance, a new entry is inserted; the stale one is skipped later."] },
  { id: "astar", name: "A* Search", type: "min", key: "f = g + h", blurb: "Expand the node that looks cheapest overall.", items: [["Start", 6], ["Node n1", 9], ["Node n2", 7]], incoming: [["Node n3", 8], ["Goal", 8]], how: ["The open set is a min-heap keyed by f = g + h.", "extractMin returns the most promising node.", "Neighbours are inserted with updated f-scores."] },
];
function AppSim({ app }) {
  const { bump } = useCtx();
  const mkItems = () => { let cur = []; app.items.forEach(([l, v], k) => { cur = opInsert(cur, app.type, { id: uid(), v, t: k, label: l }).arr; }); return cur; };
  const [heap, setHeap] = useState(mkItems);
  const [inc, setInc] = useState(0);
  const [log, setLog] = useState([]);
  const p = usePlayer();
  const step = p.step, view = step ? step.arr : heap;
  const add = () => { const [l, v] = app.incoming[inc]; const r = opInsert(heap, app.type, { id: uid(), v, t: 100 + inc, label: l }); setHeap(r.arr); p.load(r.steps); setInc(inc + 1); setLog((x) => [...x, `Arrived: ${l} (${v})`]); bump({ ops: 1, cmps: r.st.c, swaps: r.st.s, explore: "Insert" }); };
  const next = () => { const t = heap[0], r = opExtract(heap, app.type); setHeap(r.arr); p.load(r.steps); setLog((x) => [...x, `Processed: ${t.label} (${t.v})`]); bump({ ops: 1, cmps: r.st.c, swaps: r.st.s, explore: app.type === "min" ? "Extract Min" : "Extract Max" }); };
  return (
    <div className="space-y-3">
      <p className="text-sm">{app.blurb} <span className="mu">Key: {app.key} · {app.type === "min" ? "min-heap" : "max-heap"}</span></p>
      <ul className="text-sm list-disc pl-5 space-y-1">{app.how.map((h) => <li key={h}>{h}</li>)}</ul>
      <div className="flex flex-wrap gap-2">
        <button className="btn btn-c" disabled={!heap.length} onClick={next}><Play size={14} />Process next</button>
        <button className="btn" disabled={inc >= app.incoming.length} onClick={add}><Plus size={14} />{inc < app.incoming.length ? `Add ${app.incoming[inc][0]}` : "No more arrivals"}</button>
        <button className="btn" onClick={() => { setHeap(mkItems()); setInc(0); setLog([]); p.load([]); }}><RotateCcw size={14} />Reset</button>
      </div>
      <TreeView arr={view} size={step ? step.size : heap.length} marks={step ? step.marks : {}} showLabel type={app.type} empty="Every item has been processed. Press Reset to start again." />
      <Controls p={p} showSpeed={false} />
      {log.length > 0 && <ol className="text-xs mono mu space-y-0.5">{log.map((l, k) => <li key={k}>{k + 1}. {l}</li>)}</ol>}
    </div>
  );
}
function AppsPage() {
  const [sel, setSel] = useState("cpu");
  const app = APPS.find((a) => a.id === sel);
  return (
    <div>
      <PageHead title="Real-World Applications" sub="Pick a scenario and watch a heap decide what happens next." />
      <div className="grid sm:grid-cols-2 lg:grid-cols-4 gap-3 mb-4">
        {APPS.map((a) => <button key={a.id} onClick={() => setSel(a.id)} className="glass p-3 text-left" style={{ cursor: "pointer", color: "inherit", borderColor: sel === a.id ? "var(--cy)" : undefined }}><div className="font-semibold text-sm">{a.name}</div><div className="mu text-xs mt-1">{a.blurb}</div></button>)}
      </div>
      <Card title={app.name} icon={Boxes}><AppSim key={app.id} app={app} /></Card>
    </div>
  );
}

/* ============================ LEARN ============================ */
function MiniDemo({ vals, type = "min", heap = true, ops, showIdx }) {
  const init = () => (heap ? buildNow(vals, type) : mk(vals));
  const [items, setItems] = useState(init);
  const p = usePlayer("normal");
  const step = p.step, arr = step ? step.arr : items;
  const act = {
    insert: ["Insert a random value", () => { if (items.length >= 15) return; const r = opInsert(items, type, { id: uid(), v: rndInt(1, 30) }); setItems(r.arr); p.load(r.steps); }],
    extract: ["Extract the root", () => { if (!items.length) return; const r = opExtract(items, type); setItems(r.arr); p.load(r.steps); }],
    append: ["Add the next node", () => { if (items.length >= 15) return; const it = { id: uid(), v: rndInt(1, 30) }, a = [...items, it]; setItems(a); p.load([{ arr: a, size: a.length, marks: { new: [a.length - 1] }, title: `Placed at index ${a.length - 1}: the next free slot, left to right`, cmps: 0, swaps: 0, checked: 0 }], false); }],
    build: ["Build heap", () => { const r = opBuild(items, type); setItems(r.arr); p.load(r.steps); }],
    heapify: ["Heapify the root", () => { const r = opHeapifyAt(items, type, 0); setItems(r.arr); p.load(r.steps); }],
    sort: ["Run heap sort", () => { const r = opSort(items, "asc"); setItems(r.arr); p.load(r.steps); }],
    reset: ["Reset", () => { setItems(init()); p.load([]); }],
  };
  return (
    <div>
      <TreeView arr={arr} size={step ? step.size : arr.length} marks={step ? step.marks : {}} type={type} showIdx={showIdx} minLv={3} empty="The heap is empty. Insert a value or reset the demo." />
      <ArrayView arr={arr} size={step ? step.size : arr.length} marks={step ? step.marks : {}} />
      <p className="text-xs mu min-h-[2.4em] mt-1">{step ? step.title : "Try the buttons below."}</p>
      <div className="flex flex-wrap gap-2 mt-1">{[...ops, "reset"].map((o) => <button key={o} className="btn" onClick={act[o][1]}>{act[o][0]}</button>)}</div>
    </div>
  );
}
const TOPICS = [
  { t: "What is a heap?", s: "A heap is a tree where every parent is ranked above its children. The most important element is always at the top.", e: "In a min-heap of 1, 3, 2, the 1 sits on top because it is the smallest.", k: "A heap gives instant access to the best element.", d: { vals: [8, 3, 5, 1, 2], ops: ["insert", "extract"] } },
  { t: "What is a binary heap?", s: "A binary heap is a heap shaped as a complete binary tree: each node has at most two children and levels fill left to right. That shape fits neatly in an array.", e: "Index 0 is the root; its children are indexes 1 and 2.", k: "Binary heap = complete tree + heap property.", d: { vals: [4, 9, 6, 12, 10, 7], ops: ["insert", "extract"], showIdx: true } },
  { t: "Complete binary tree", s: "Every level is full except maybe the last, and the last level is filled from the left. No gaps are allowed.", e: "Adding a node always uses the next array index.", k: "Completeness is why the array needs no pointers.", d: { vals: [4, 9, 2, 7], heap: false, ops: ["append"], showIdx: true } },
  { t: "Min heap", s: "Every parent is smaller than or equal to its children. The minimum is the root.", e: "Parent 2 with children 5 and 3 is fine; parent 6 with child 4 is not.", k: "Min-heap: smallest first.", d: { vals: [7, 3, 9, 1, 5, 8], type: "min", ops: ["insert", "extract"] } },
  { t: "Max heap", s: "Every parent is larger than or equal to its children. The maximum is the root.", e: "Parent 30 with children 12 and 25 is fine.", k: "Max-heap: largest first.", d: { vals: [7, 3, 9, 1, 5, 8], type: "max", ops: ["insert", "extract"] } },
  { t: "Heap operations", s: "Insert adds at the end and moves up. Extract removes the root, moves the last element to the top and moves it down. Both walk one root-to-leaf path.", e: "With 1000 elements the path has about 10 levels.", k: "Insert and extract cost O(log n).", d: { vals: [2, 5, 4, 9, 8, 7], ops: ["insert", "extract"] } },
  { t: "Heapify", s: "Heapify fixes one node by sinking it: compare with the better child, swap if needed, continue downward.", e: "Here the root 9 is too big, so it sinks past 2 and 4.", k: "Heapify repairs one broken node in O(log n).", d: { vals: [9, 2, 3, 4, 5, 6, 7], heap: false, ops: ["heapify"] } },
  { t: "Build heap", s: "To heapify a whole array, start at the last non-leaf node and heapify backwards to the root.", e: "Most nodes are near the bottom and barely move, so the total work is linear.", k: "Build heap costs O(n).", d: { vals: [9, 4, 7, 1, 2, 6, 3], heap: false, ops: ["build"] } },
  { t: "Heap sort", s: "Build a max-heap, swap the root with the last element, shrink the heap, heapify, repeat. The array ends up sorted.", e: "Each round puts the next largest value in its final place.", k: "Heap sort is O(n log n) and in place.", d: { vals: [5, 3, 8, 1, 9, 2], heap: false, ops: ["sort"] } },
  { t: "Priority queue", s: "A priority queue serves the most urgent item first. A binary heap is the usual way to build one.", e: "Insert = enqueue, extract = dequeue the highest priority.", k: "Priority queue = abstract idea, heap = implementation.", d: { vals: [3, 6, 4, 9, 7], ops: ["insert", "extract"] } },
  { t: "Applications", s: "Heaps power schedulers, shortest-path search, event simulators, top-K queries and heap sort.", e: "Dijkstra's algorithm extracts the nearest vertex from a min-heap each round.", k: "Wherever “what is next?” matters, think heap.", d: null },
];
function LearnPage() {
  const { go } = useCtx();
  const [k, setK] = useState(0);
  const T = TOPICS[k];
  return (
    <div>
      <PageHead title="Learn" sub="Short lessons, each with a demo you can poke." />
      <div className="grid lg:grid-cols-4 gap-4">
        <div className="flex lg:flex-col gap-1.5 overflow-x-auto pb-1">
          {TOPICS.map((x, i) => <button key={x.t} className={`btn ${i === k ? "btn-p" : ""}`} style={{ whiteSpace: "nowrap", justifyContent: "flex-start" }} onClick={() => setK(i)}>{x.t}</button>)}
        </div>
        <div className="lg:col-span-3 space-y-4">
          <Card title={T.t} icon={GraduationCap}>
            <p className="leading-relaxed max-w-prose">{T.s}</p>
            <p className="text-sm mu mt-2">Example: {T.e}</p>
            <p className="font-semibold mt-3 tcy">Key takeaway: {T.k}</p>
          </Card>
          <Card title="Interactive demo" icon={Play}>
            {T.d ? <MiniDemo key={k} {...T.d} /> : <div><p className="text-sm mu mb-3">See heaps working inside eight real systems.</p><button className="btn btn-p" onClick={() => go("apps")}>Open applications<ChevronRight size={14} /></button></div>}
          </Card>
          <div className="flex gap-2">
            <button className="btn" disabled={k === 0} onClick={() => setK(k - 1)}>Previous topic</button>
            <button className="btn btn-p" disabled={k === TOPICS.length - 1} onClick={() => setK(k + 1)}>Next topic</button>
          </div>
        </div>
      </div>
    </div>
  );
}

/* ============================ CODE LAB ============================ */
const CODE = {
  Python: {
    Insert: `def insert(self, x):
    self.a.append(x)
    i = len(self.a) - 1
    while i > 0 and self.a[(i - 1) // 2] > self.a[i]:
        p = (i - 1) // 2
        self.a[i], self.a[p] = self.a[p], self.a[i]
        i = p`,
    Delete: `def delete(self, i=0):
    if i >= len(self.a):
        raise IndexError("empty heap or bad index")
    removed = self.a[i]
    last = self.a.pop()
    if i < len(self.a):
        self.a[i] = last
        if i > 0 and self.a[i] < self.a[(i - 1) // 2]:
            self._up(i)
        else:
            self._down(i, len(self.a))
    return removed`,
    Heapify: `def _up(self, i):
    while i > 0 and self.a[i] < self.a[(i - 1) // 2]:
        p = (i - 1) // 2
        self.a[i], self.a[p] = self.a[p], self.a[i]
        i = p

def _down(self, i, n):
    while True:
        l, r, s = 2 * i + 1, 2 * i + 2, i
        if l < n and self.a[l] < self.a[s]: s = l
        if r < n and self.a[r] < self.a[s]: s = r
        if s == i:
            break
        self.a[i], self.a[s] = self.a[s], self.a[i]
        i = s`,
    "Build Heap": `def build_heap(self, arr):
    self.a = list(arr)
    for i in range(len(self.a) // 2 - 1, -1, -1):
        self._down(i, len(self.a))`,
    "Heap Sort": `def heap_sort(arr):
    a, n = list(arr), len(arr)
    def down(i, n):
        while True:
            l, r, s = 2 * i + 1, 2 * i + 2, i
            if l < n and a[l] > a[s]: s = l
            if r < n and a[r] > a[s]: s = r
            if s == i:
                break
            a[i], a[s] = a[s], a[i]
            i = s
    for i in range(n // 2 - 1, -1, -1):
        down(i, n)
    for end in range(n - 1, 0, -1):
        a[0], a[end] = a[end], a[0]
        down(0, end)
    return a`,
  },
  Java: {
    Insert: `void insert(int x) {
    a.add(x);
    int i = a.size() - 1;
    while (i > 0 && a.get((i - 1) / 2) > a.get(i)) {
        Collections.swap(a, i, (i - 1) / 2);
        i = (i - 1) / 2;
    }
}`,
    Delete: `int delete(int i) {
    int removed = a.get(i);
    int last = a.remove(a.size() - 1);
    if (i < a.size()) {
        a.set(i, last);
        if (i > 0 && a.get(i) < a.get((i - 1) / 2)) up(i);
        else down(i, a.size());
    }
    return removed;
}`,
    Heapify: `void up(int i) {
    while (i > 0 && a.get(i) < a.get((i - 1) / 2)) {
        Collections.swap(a, i, (i - 1) / 2);
        i = (i - 1) / 2;
    }
}

void down(int i, int n) {
    while (true) {
        int l = 2 * i + 1, r = l + 1, s = i;
        if (l < n && a.get(l) < a.get(s)) s = l;
        if (r < n && a.get(r) < a.get(s)) s = r;
        if (s == i) break;
        Collections.swap(a, i, s);
        i = s;
    }
}`,
    "Build Heap": `void buildHeap(int[] arr) {
    a = new ArrayList<>();
    for (int v : arr) a.add(v);
    for (int i = a.size() / 2 - 1; i >= 0; i--)
        down(i, a.size());
}`,
    "Heap Sort": `static void siftDown(int[] a, int i, int n) {
    while (true) {
        int l = 2 * i + 1, r = l + 1, s = i;
        if (l < n && a[l] > a[s]) s = l;
        if (r < n && a[r] > a[s]) s = r;
        if (s == i) break;
        int t = a[i]; a[i] = a[s]; a[s] = t;
        i = s;
    }
}

static void heapSort(int[] a) {
    int n = a.length;
    for (int i = n / 2 - 1; i >= 0; i--) siftDown(a, i, n);
    for (int end = n - 1; end > 0; end--) {
        int t = a[0]; a[0] = a[end]; a[end] = t;
        siftDown(a, 0, end);
    }
}`,
  },
  "C++": {
    Insert: `void insert(int x) {
    a.push_back(x);
    int i = a.size() - 1;
    while (i > 0 && a[(i - 1) / 2] > a[i]) {
        swap(a[i], a[(i - 1) / 2]);
        i = (i - 1) / 2;
    }
}`,
    Delete: `int remove(int i = 0) {
    int removed = a[i];
    a[i] = a.back();
    a.pop_back();
    if (i < (int)a.size()) {
        if (i > 0 && a[i] < a[(i - 1) / 2]) up(i);
        else down(i, a.size());
    }
    return removed;
}`,
    Heapify: `void up(int i) {
    while (i > 0 && a[i] < a[(i - 1) / 2]) {
        swap(a[i], a[(i - 1) / 2]);
        i = (i - 1) / 2;
    }
}

void down(int i, int n) {
    while (true) {
        int l = 2 * i + 1, r = l + 1, s = i;
        if (l < n && a[l] < a[s]) s = l;
        if (r < n && a[r] < a[s]) s = r;
        if (s == i) break;
        swap(a[i], a[s]);
        i = s;
    }
}`,
    "Build Heap": `void buildHeap(const vector<int>& arr) {
    a = arr;
    for (int i = (int)a.size() / 2 - 1; i >= 0; i--)
        down(i, a.size());
}`,
    "Heap Sort": `void siftDown(vector<int>& a, int i, int n) {
    while (true) {
        int l = 2 * i + 1, r = l + 1, s = i;
        if (l < n && a[l] > a[s]) s = l;
        if (r < n && a[r] > a[s]) s = r;
        if (s == i) break;
        swap(a[i], a[s]);
        i = s;
    }
}

void heapSort(vector<int>& a) {
    int n = a.size();
    for (int i = n / 2 - 1; i >= 0; i--) siftDown(a, i, n);
    for (int end = n - 1; end > 0; end--) {
        swap(a[0], a[end]);
        siftDown(a, 0, end);
    }
}`,
  },
};
function copyText(t) {
  if (navigator.clipboard && navigator.clipboard.writeText) return navigator.clipboard.writeText(t).catch(() => fallbackCopy(t));
  fallbackCopy(t); return Promise.resolve();
}
function fallbackCopy(t) { const a = document.createElement("textarea"); a.value = t; a.style.position = "fixed"; a.style.opacity = "0"; document.body.appendChild(a); a.select(); try { document.execCommand("copy"); } catch (e) {} document.body.removeChild(a); }
function CodePage() {
  const [lang, setLang] = useState("Python");
  const [sec, setSec] = useState("Insert");
  const [ok, setOk] = useState(false);
  const code = CODE[lang][sec];
  const copy = () => { copyText(code); setOk(true); setTimeout(() => setOk(false), 1500); };
  return (
    <div>
      <PageHead title="Code Lab" sub="Reference implementations of a binary min-heap. Code is shown for study and copying; nothing is executed here." />
      <Card>
        <div className="flex flex-wrap gap-2 items-center mb-3">
          <Seg value={lang} onChange={setLang} options={Object.keys(CODE).map((l) => [l, l])} />
          <Seg value={sec} onChange={setSec} options={Object.keys(CODE.Python).map((s) => [s, s])} />
          <button className="btn btn-p ml-auto" onClick={copy}><Copy size={14} />{ok ? "Copied" : "Copy code"}</button>
        </div>
        <pre className="code">{code}</pre>
        <p className="text-xs mu mt-2">{sec === "Heap Sort" ? "Heap sort uses a max-heap so the array ends up in ascending order." : "This is a min-heap. For a max-heap, flip each comparison (< becomes >)."}{sec === "Delete" ? " The helpers up and down are in the Heapify section." : ""}</p>
      </Card>
    </div>
  );
}

/* ============================ JOURNEY + ABOUT ============================ */
const ALL_ALGOS = ["Insert", "Delete", "Extract Min", "Extract Max", "Heapify", "Build Heap", "Heap Sort"];
function JourneyPage() {
  const { stats } = useCtx();
  const pts = stats.ops + stats.explored.length * 3 + stats.done * 5;
  const stars = Math.min(5, 1 + Math.floor(pts / 25));
  const title = stars <= 2 ? "Heap Explorer" : stars === 3 ? "Heap Builder" : stars === 4 ? "Heap Master" : "Algorithm Architect";
  return (
    <div>
      <PageHead title="Your Heap Journey" sub="Everything you have done in this session." />
      <Card className="text-center py-6">
        <p className="mu text-sm">{title} level</p>
        <p className="text-4xl my-2" style={{ color: "var(--cmp)", letterSpacing: 4 }} aria-label={`${stars} of 5 stars`}>{"★".repeat(stars)}<span style={{ opacity: 0.25 }}>{"★".repeat(5 - stars)}</span></p>
        <p className="mu text-xs">Earn stars by running operations, exploring algorithms and answering challenges.</p>
      </Card>
      <div className="grid grid-cols-2 md:grid-cols-4 gap-3 mt-4">
        <Tile label="Operations performed" value={stats.ops} /><Tile label="Elements processed" value={stats.processed} />
        <Tile label="Comparisons" value={stats.cmps} /><Tile label="Swaps" value={stats.swaps} />
        <Tile label="Challenges completed" value={`${stats.done}/${stats.total}`} /><Tile label="Best challenge score" value={stats.best} />
        <Tile label="Algorithms explored" value={`${stats.explored.length}/${ALL_ALGOS.length}`} />
      </div>
      <Card className="mt-4" title="Algorithms explored" icon={Compass}>
        <div className="flex flex-wrap gap-2">{ALL_ALGOS.map((a) => <span key={a} className="chip" style={stats.explored.includes(a) ? { borderColor: "var(--new)", color: "var(--new)" } : { opacity: 0.55 }}>{stats.explored.includes(a) ? "✓ " : ""}{a}</span>)}</div>
      </Card>
    </div>
  );
}
function AboutPage() {
  const S = [
    ["Problem", "Heaps are taught with static diagrams, but their behaviour is dynamic: elements move, swap and sink. Students struggle to connect the picture of a tree with the array that actually stores it."],
    ["Existing learning difficulty", "Textbook figures show only the before and after of an operation. The reasoning in between (which comparison, why a swap) stays invisible, and index formulas feel abstract."],
    ["Proposed solution", "HEAPVERSE is an interactive laboratory. Every operation runs on a real array and is animated one step at a time, with a tree view and an array view that always agree."],
    ["Objectives", "Visualize insert, delete, extract, heapify, build heap and heap sort. Make index arithmetic tangible. Show priority queues in real systems. Test understanding with challenges."],
    ["Technologies used", "React, Tailwind-style utility classes with custom CSS, Lucide icons, Recharts for charts, SVG and CSS transitions for animation. All state lives in the browser; there is no backend."],
    ["DSA concepts", "Complete binary tree, heap property, array representation, sift-up and sift-down, bottom-up build heap (O(n)), heap sort (O(n log n)), priority queues, Dijkstra and A*."],
    ["Future scope", "Fibonacci and d-ary heaps, decrease-key, a step-by-step comparison with quicksort and merge sort, saved sessions and a teacher dashboard."],
  ];
  return (
    <div>
      <PageHead title="About the Project" />
      <Card>
        <dl className="grid sm:grid-cols-3 gap-4 text-sm">
          <div><dt className="mu text-xs">Project title</dt><dd className="font-semibold">HEAPVERSE</dd></div>
          <div><dt className="mu text-xs">Subject</dt><dd className="font-semibold">Data Structures and Algorithms</dd></div>
          <div><dt className="mu text-xs">Topic</dt><dd className="font-semibold">Heap and Binary Heap</dd></div>
        </dl>
        <p className="mt-4 text-sm"><span className="mu">Purpose: </span>To provide an interactive visual environment for understanding heap-based data structures and algorithms.</p>
      </Card>
      <div className="grid md:grid-cols-2 gap-4 mt-4">{S.map(([t, d]) => <Card key={t} title={t}><p className="text-sm leading-relaxed">{d}</p></Card>)}</div>
    </div>
  );
}

/* ============================ APP SHELL ============================ */
const PAGES = [
  ["dash", "Dashboard", LayoutDashboard, Dashboard], ["lab", "Heap Lab", FlaskConical, HeapLab], ["binary", "Binary Heap", Network, BinaryHeapPage],
  ["compare", "Min vs Max", GitCompare, ComparePage], ["heapify", "Heapify", Wand2, HeapifyPage], ["sort", "Heap Sort", ArrowDownUp, SortPage],
  ["pq", "Priority Queue", ListOrdered, PQPage], ["algo", "Algorithm Explorer", Compass, AlgoPage], ["repair", "Validate & Repair", ShieldCheck, RepairPage],
  ["builder", "Drag Builder", Hammer, BuilderPage], ["challenge", "Challenge Arena", Trophy, ChallengePage], ["complexity", "Complexity Lab", Activity, ComplexityPage],
  ["apps", "Applications", Boxes, AppsPage], ["code", "Code Lab", Code2, CodePage], ["learn", "Learn", GraduationCap, LearnPage],
  ["journey", "Your Journey", Flag, JourneyPage], ["about", "About Project", Info, AboutPage],
];
export default function App() {
  const [page, setPage] = useState("landing");
  const [theme, setTheme] = useState("dark");
  const [speed, setSpeed] = useState("normal");
  const [type, setType] = useState("min");
  const [heap, setHeap] = useState([]);
  const [labInput, setLabInput] = useState("50, 20, 40, 10, 30, 60, 5");
  const [op, setOp] = useState({ name: "Idle", busy: false });
  const [nav, setNav] = useState(false);
  const [stats, setStats] = useState({ ops: 0, cmps: 0, swaps: 0, processed: 0, done: 0, total: 0, best: 0, explored: [] });
  const bump = (o) => setStats((s) => ({
    ...s, ops: s.ops + (o.ops || 0), cmps: s.cmps + (o.cmps || 0), swaps: s.swaps + (o.swaps || 0), processed: s.processed + (o.processed || 0),
    done: s.done + (o.done || 0), total: s.total + (o.total || 0), best: Math.max(s.best, o.score || 0),
    explored: o.explore && !s.explored.includes(o.explore) ? [...s.explored, o.explore] : s.explored,
  }));
  const go = (pg) => { setPage(pg); setNav(false); if (typeof window !== "undefined" && window.scrollTo) window.scrollTo(0, 0); };
  const ctx = { page, go, theme, speed, setSpeed, type, setType, heap, setHeap, labInput, setLabInput, op, setOp, stats, bump };
  const cur = PAGES.find((x) => x[0] === page);
  const Page = cur ? cur[3] : null;
  const themeBtn = <button className="btn" onClick={() => setTheme(theme === "dark" ? "light" : "dark")} aria-label="Toggle light and dark mode" title="Toggle light / dark">{theme === "dark" ? <Sun size={15} /> : <Moon size={15} />}</button>;
  return (
    <Ctx.Provider value={ctx}>
      <div className={`hv ${theme === "light" ? "light" : ""}`}>
        <style>{CSS}</style>
        {page === "landing" ? (
          <div className="relative"><div className="absolute right-4 top-4 z-10" style={{ marginTop: 58 }}>{themeBtn}</div><Landing /></div>
        ) : (
          <div className="flex min-h-screen">
            {nav && <div className="fixed inset-0 z-20 lg:hidden" style={{ background: "rgba(0,0,0,.5)" }} onClick={() => setNav(false)} />}
            <aside className={`fixed lg:sticky top-0 z-30 h-screen w-64 shrink-0 overflow-y-auto p-3 ${nav ? "" : "-translate-x-full lg:translate-x-0"}`} style={{ background: "var(--bg)", borderRight: "1px solid var(--line)", transition: "transform .25s" }} aria-label="Main navigation">
              <button className="font-bold tracking-widest text-sm px-2 py-3 text-left" style={{ cursor: "pointer", background: "none", border: 0, color: "var(--tx)" }} onClick={() => go("landing")}>HEAPVERSE</button>
              <nav className="space-y-0.5 mt-1">
                {PAGES.map(([id, label, I]) => (
                  <button key={id} onClick={() => go(id)} className="flex items-center gap-2.5 w-full px-3 py-2 rounded-lg text-sm text-left" aria-current={page === id ? "page" : undefined}
                    style={{ cursor: "pointer", border: "1px solid " + (page === id ? "var(--cur)" : "transparent"), background: page === id ? "rgba(139,92,246,.2)" : "transparent", color: page === id ? "var(--tx)" : "var(--mu)", fontWeight: page === id ? 600 : 500 }}>
                    <I size={16} />{label}
                  </button>
                ))}
              </nav>
            </aside>
            <main className="flex-1 min-w-0">
              <header className="sticky top-0 z-10 flex flex-wrap items-center gap-2 px-4 py-2.5" style={{ background: "color-mix(in srgb, var(--bg) 88%, transparent)", backdropFilter: "blur(10px)", borderBottom: "1px solid var(--line)" }}>
                <button className="btn lg:hidden" onClick={() => setNav(!nav)} aria-label="Open navigation">{nav ? <X size={15} /> : <Menu size={15} />}</button>
                <span className="font-bold tracking-widest text-sm mr-1">HEAPVERSE</span>
                <span className="chip"><span className={`inline-block w-2 h-2 rounded-full ${op.busy ? "pulse" : ""}`} style={{ background: op.busy ? "var(--cmp)" : "var(--new)" }} />{op.busy ? "Animating" : "System ready"}</span>
                <span className="chip hidden sm:inline-flex">{typeName(type)}</span>
                <span className="chip hidden sm:inline-flex">{heap.length} node{heap.length === 1 ? "" : "s"}</span>
                <span className="chip hidden md:inline-flex" style={{ maxWidth: 260, overflow: "hidden", whiteSpace: "nowrap", textOverflow: "ellipsis" }}>{op.name}</span>
                <span className="ml-auto">{themeBtn}</span>
              </header>
              <div className="p-4 md:p-6 page max-w-7xl mx-auto" key={page}>{Page && <Page />}</div>
            </main>
          </div>
        )}
      </div>
    </Ctx.Provider>
  );
}
