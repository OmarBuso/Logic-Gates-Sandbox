/*

Read this first, it'll save you an afternoon

Sections, in file order:
    1. State + constants
    2. Geometry + block helpers
    3. Simulation engine
    4. Persistence
    5. Undo/Redo
    6. Rendering
    7. Board editing (taps)
    8. Palette, modes, toasts, example boards
    9. Truth tables
    10. Pin settings & editing abstract blocks
    11. Tutorial
    12. Menu + modals
    13. Settings and reset
    14. Input: Pan/pinch/wheel
    15. Boot

Naming cheat sheet (terse on purpose; renaming it all is a different project):
    b      a block      {id, t, x, y, w, h, slots, v, label, d?}
    t      block type   'io' | 'not' | 'and' | 'abs' (abstract = user-made block)
    q / s  a slot, i.e. one arrow on a block's edge: [x, y, dir, kind, pin?, label?]
    dir    index into D: 0 up, 1 right, 2 down, 3 left
    kind   1 = input arrow (points into the block), 2 = output arrow (points out)
    d      a definition  {name, color, ports, blocks}  (what an abstract block contains)
    port   a pin of a definition {id, pin, label, k}; k=1 input pin, k=2 output pin
    n      a simulation node {key, k (type), v (value 0/1), ins, src, need, hasIn}
    H      handles from build(): block id -> {n?, out(slot), set(slot, src)}
    G      board bounds in cells {x0, y0, x1, y1}
    cam    camera {x, y, s} where s = pixels per cell

How an edit flows: change blocks/defs/G  ->  commit()  ->  rebuild() flattens
everything into nodes  ->  step() runs on a timer  ->  draw() repaints when dirty

Single-letter names were a choice
I'd defend it, but only on a good day

*/

// I tried organizing this once. The code fought back. Now we have globals
// Everything mutates everything directly because passing state around properly
// turned this into a verbose nightmare. May the JavaScript gods have mercy on my soul


/*
1. State + Constants
D: the four directions as [dx, dy], clockwise from up (0 up, 1 right, 2 down, 3 left)
MAXN: biggest board (or block) side, in cells
*/

const D = [
        [0, -1],
        [1, 0],
        [0, 1],
        [-1, 0]
    ],
    MAXN = 64,
    $ = s => document.querySelector(s);
const esc = s => String(s).replace(/[&<>"]/g, c => ({
    '&': '&amp;',
    '<': '&lt;',
    '>': '&gt;',
    '"': '&quot;'
} [c]));
// One colour per block type, plus the yellow that means "this is 1"
// Yes, yellow 
// No, i will not be taking questions
const COL = {
        io: '#f4f4f4',
        not: '#e57373',
        and: '#6f9bf0'
    },
    ON = '#ffd54a';
let G = { x0: 0, y0: 0, x1: 12, y1: 12 },  // board bounds in cells (grows via the + tiles)
    speed = 16,            // simulation steps per second
    paused = 0,            // 1 while paused (Settings -> Pause)
    blocks = [],           // every block on the board currently shown
    defs = {},             // abstract block definitions, keyed by ids like 'dmv6s8k05'
    nid = 1,               // next free block id
    mode = 'view',         // 'view' (flip switches) or 'build' (edit the board)
    tool = null,           // palette pick: 'io' | 'not' | 'and' | a defs key | null
    sel = null,            // selected block w/build mode
    showLab = true,        // the label toggle that will definitely help you a lot turning it off when you have really long pin names
    cmap = {},             // "x,y" -> block lookup, rebuilt constantly
    H = {},                // handles from build(); half the file leans on this
    nodes = [],            // flat list of simulation nodes
    dirty = 1,             // 1 = repaint next frame. When in doubt, set it.
    dpr = 1,               // devicePixelRatio, for a crisp canvas
    inited = 0,            // 1 once the first ResizeObserver tick has happened
    editingDefKey = null,  // key of the abstract block being edited, if any
    editReturn = null,     // the board we go back to afterwards. Hold it tightly.
    pinEdit = null,        // which pin the Pin settings dialog is editing
    probing = false;       // "Truth tables: on" mode
// Undo/redo snapshots. Whole-board copies are wasteful. Has that ever mattered? No.
let hist = [], histIdx = -1, histBusy = false;
const inB = (x, y) => x >= G.x0 && y >= G.y0 && x < G.x1 && y < G.y1,
    cam = {
        x: 0,
        y: 0,
        s: 60
    },
    wire = new WeakMap(),
    cv = $('#cv'),
    ctx = cv.getContext('2d');


/*
2. Geometry + Block helpers
Cell lookups, pin naming, abstract-block pin layout, block factory
*/

// Maps every occupied cell "x,y" to the block covering it
const cellMap = l => {
    const m = {};
    for (const b of l)
        for (let i = 0; i < b.w; i++)
            for (let j = 0; j < b.h; j++) m[b.x + i + ',' + (b.y + j)] = b;
    return m
};
const pinName = p => String(p?.pin ?? p?.label ?? '');
const resolvePin = (d, name, k) => d?.ports?.find(p => pinName(p) === String(name ?? '') && p.k === k) || null;
const pinInvalid = (b, q) => {
    if (b.t !== 'abs') return false;
    const d = defs[b.d];
    if (!resolvePin(d, q[4], q[3])) return true;
    if (q[3] === 1) {
        const i = b.slots.indexOf(q);
        return b.slots.slice(0, i).some(z => z[3] === 1 && String(z[4] ?? '') === String(q[4] ?? ''))
    }
    return false
};

// Spreads an abstract block's pins around its perimeter
// Inputs fill left, top, bottom, right; outputs fill right, bottom, top, left
// keep=1 re-lays out the pins the block already has (after a resize) instead of the definition's defaults
function layoutAbs(b, keep) {
    const def = defs[b.d],
        ports = def?.ports || [],
        capacity = 2 * (b.w + b.h);
    const old = keep ? (b.slots || []).map(q => [String(q[4] ?? ''), String(q[5] ?? '~'), q[3]]) :
        ports.slice(0, capacity).map(p => [pinName(p), '~', p.k]);
    const specs = old.slice(0, capacity);
    const S = [
        [],
        [],
        [],
        []
    ];
    for (let j = 0; j < b.w; j++) {
        S[0].push([b.x + j, b.y]);
        S[2].push([b.x + j, b.y + b.h - 1])
    }
    for (let i = 0; i < b.h; i++) {
        S[3].push([b.x, b.y + i]);
        S[1].push([b.x + b.w - 1, b.y + i])
    }
    b.slots = [];
    const put = (L, order, k) => {
        for (const z of L) {
            const d = order.find(d => S[d].length);
            if (d === undefined) break;
            const q = S[d].shift();
            b.slots.push([q[0], q[1], d, k, z[0], z[1]])
        }
    };
    put(specs.filter(z => z[2] === 1), [3, 0, 2, 1], 1);
    put(specs.filter(z => z[2] === 2), [1, 2, 0, 3], 2)
}

// Block factory. NOT and AND arrive with default arrows (NOT: in left, out right;
// AND: in left, in top, out right). "e" overrides fields, e.g. {d: defKey} for abstract blocks.
// I sometimes wonder if blocks should be classes. Then I look at the rest of the file and stop wondering
function mk(t, x, y, e) {
    const b = {
        id: nid++,
        t,
        x,
        y,
        w: 1,
        h: 1,
        slots: [],
        v: 0,
        label: ''
    };
    if (t == 'not') b.slots = [
        [x, y, 3, 1],
        [x, y, 1, 2]
    ];
    if (t == 'and') b.slots = [
        [x, y, 3, 1],
        [x, y, 0, 1],
        [x, y, 1, 2]
    ];
    Object.assign(b, e);
    if (t == 'abs') layoutAbs(b);
    return b
}

/*
3. Simulation Engine
build() flattens blocks into nodes, classify() sorts them into loops vs. feed-forward,
step() advances the whole circuit by one tick
*/

// Any input wired to nothing reads from here: a permanent, lonely 0
const DEAD = {
    v: 0
};

// The Scary Recursive Function™
// I spent three days staring at a wall to write this
// It flattens abstract nested blocks into the 1D hellscape the sim actually runs on "pre" prevents nested copies of the same block from colliding 
// If you touch the claimedInputs set, I will personally haunt your codebase
function build(list, out, pre) {
    pre = pre || '';
    const h = {},
        cm = cellMap(list);
    for (const b of list) {
        if (b.t == 'abs') {
            const d = defs[b.d],
                inner = build(d.blocks, out, pre + b.id + '/'),
                claimedInputs = new Set();
            h[b.id] = {
                out: s => {
                    const p = resolvePin(d, s[4], 2),
                        target = p && inner[p.id];
                    return target ? target.out(s) : DEAD
                },
                set: (s, src) => {
                    const name = String(s[4] ?? ''),
                        first = b.slots.find(q => q[3] === 1 && String(q[4] ?? '') === name);
                    if (first !== s) return;
                    const p = resolvePin(d, name, 1),
                        target = p && inner[p.id];
                    if (!target || claimedInputs.has(name)) return;
                    claimedInputs.add(name);
                    target.set(s, src)
                }
            }
        } else {
            const n = {
                key: pre + b.id,
                k: b.t,
                v: b.t == 'io' ? b.v : 0,
                ins: [],
                src: null,
                need: b.slots.filter(s => s[3] == 1).length,
                hasIn: b.slots.some(s => s[3] == 1)
            };
            out.push(n);
            h[b.id] = {
                n,
                out: () => n,
                set: (s, src) => {
                    n.src = src;
                    n.ins.push(src)
                }
            }
        }
    }
    for (const b of list)
        for (const s of b.slots)
            if (s[3] == 2) {
                const dv = D[s[2]],
                    nx = s[0] + dv[0],
                    ny = s[1] + dv[1],
                    nb = cm[nx + ',' + ny];
                if (!nb || nb === b) continue;
                const t = nb.slots.find(q => q[0] == nx && q[1] == ny && q[2] == (s[2] + 2) % 4 && q[3] == 1);
                if (t) {
                    const src = h[b.id].out(s);
                    h[nb.id].set(t, src);
                    wire.set(t, src)
                }
            }
    return h
}

// The single source of truth for node evaluation. I used to have two copies of this logic (one for fixed points, one for the real tick)
// and they immediately drifted out of sync because of course they did
// One copy now, read it and weep
// Rules: io passes its wired source along (an unwired switch keeps its own value), not flips
// and = 1 only if EVERY input arrow is wired and high (a dangling input arrow pins an AND at 0)
// Those are the only three kinds of node there are, abstract blocks are flattened away before this runs
function evalNode(n) {
    const I = n.ins,
        m = I.length;
    if (n.k == 'io') return n.src ? n.src.v : (n.hasIn ? 0 : n.v);
    if (n.k == 'not') return m && I[0].v ? 0 : 1;
    if (n.k == 'and') {
        let r = n.need > 0 && m == n.need ? 1 : 0;
        for (let i = 0; r && i < m; i++)
            if (!I[i].v) r = 0;
        return r
    }
    return 0
}

function depsOf(n) {
    const s = new Set();
    for (const d of n.ins)
        if (d && d !== DEAD) s.add(d);
    return s
}
let cyclicNodes = [],
    topoOrder = [];

// Tarjan's SCC algorithm, forcibly shoved into a logic gate sim because feedback loops are chaotic nightmares 
// We split nodes into "genuinely cyclic loops of chaos" and "nice predictable feedforward logic"
// If a graph deep enough to blow the call stack happens, we fail safe and assume absolutely everything is cursed
function classify() {
    let idx = 0;
    const index = new Map(),
        low = new Map(),
        onStack = new Set(),
        stack = [];
    const visit = v => {
        index.set(v, idx);
        low.set(v, idx);
        idx++;
        stack.push(v);
        onStack.add(v);
        for (const w of depsOf(v)) {
            if (!index.has(w)) {
                visit(w);
                low.set(v, Math.min(low.get(v), low.get(w)))
            } else if (onStack.has(w)) low.set(v, Math.min(low.get(v), index.get(w)))
        }
        if (low.get(v) === index.get(v)) {
            const members = [];
            let w;
            do {
                w = stack.pop();
                onStack.delete(w);
                members.push(w)
            } while (w !== v);
            const selfLoop = members.length === 1 && depsOf(members[0]).has(members[0]);
            const cyclic = members.length > 1 || selfLoop;
            for (const m of members) m.cyclic = cyclic
        }
    };
    try {
        for (const n of nodes)
            if (!index.has(n)) visit(n)
    } catch (e) {
        // Great, everything is a loop now. This is your fault, yes, YOUR FAULT. If you werent seeing my code through inspect element this could have worked perfectly
        // How do I know that you got your F12 privileges?
        // I have eyes EVERYWHERE
        for (const n of nodes) n.cyclic = true
    }

    cyclicNodes = nodes.filter(n => n.cyclic);
    const acyclic = nodes.filter(n => !n.cyclic);

    const indeg = new Map(acyclic.map(n => [n, 0])),
        dependents = new Map(acyclic.map(n => [n, []]));
    for (const n of acyclic)
        for (const dep of depsOf(n))
            if (!dep.cyclic) {
                indeg.set(n, indeg.get(n) + 1);
                dependents.get(dep).push(n)
            }
    const q = acyclic.filter(n => indeg.get(n) === 0);
    topoOrder = [];
    while (q.length) {
        const n = q.shift();
        topoOrder.push(n);
        for (const d of dependents.get(n)) {
            indeg.set(d, indeg.get(d) - 1);
            if (indeg.get(d) === 0) q.push(d)
        }
    }
    if (topoOrder.length !== acyclic.length) {
        for (const n of nodes) n.cyclic = true;
        cyclicNodes = nodes.slice();
        topoOrder = []
    }
}

function rebuild() {
    const st = {};
    for (const n of nodes) st[n.key] = n.v;
    cmap = cellMap(blocks);
    nodes = [];
    H = build(blocks, nodes);
    for (const n of nodes)
        if (n.key in st) n.v = st[n.key];
    classify()
}

// Phase 1: The stateful spaghetti... double-buffered because order matters when everything is on fire, compute first, THEN commit
// Phase 2: The nice, predictable feedforward acyclic logic. One pass. Perfect accuracy.
// I love Phase 2, Phase 1 scares me
// do not simplify this pls
function step() {
    let c = 0;
    const CN = cyclicNodes,
        L1 = CN.length,
        nv = new Uint8Array(L1);
    for (let j = 0; j < L1; j++) nv[j] = evalNode(CN[j]);
    for (let j = 0; j < L1; j++)
        if (CN[j].v !== nv[j]) {
            CN[j].v = nv[j];
            c = 1
        }
    const TO = topoOrder,
        L2 = TO.length;
    for (let j = 0; j < L2; j++) {
        const n = TO[j],
            r = evalNode(n);
        if (n.v !== r) c = 1;
        n.v = r
    }
    return c
}

// Two clocks, on purpose: loop() ticks the sim (setTimeout, so speed can change mid-flight),
// raf() repaints, and only when something is dirty. I considered merging them. Briefly.
function loop() {
    if (!paused && step()) dirty = 1;
    setTimeout(loop, 1000 / speed);
}

function raf() {
    if (tutActive) checkTut();
    if (dirty) draw();
    requestAnimationFrame(raf)
}
setTimeout(loop, 100);
requestAnimationFrame(raf);


/*
4. Persistence (this is what i lost 3 weeks ago)
Block to array conversion, the LGS format, import validation, save/load
Bytes, varints and mild regret
sb: block -> flat array for saving; ub: the reverse
Plain blocks store 4 numbers per slot; abstract blocks store 6 (x, y, dir, kind, pin, label)
*/

const sb = b => [b.id, b.t, b.x, b.y, b.w, b.h, b.t == 'abs' ? b.slots.flatMap(q => [q[0], q[1], q[2], q[3], String(q[4] ?? ''), String(q[5] ?? '~')]) : b.slots.flat(), b.v, b.label, b.d || 0];
const ub = a => {
    const b = {
        id: a[0],
        t: a[1],
        x: a[2],
        y: a[3],
        w: a[4],
        h: a[5],
        slots: [],
        v: a[7],
        label: a[8]
    };
    if (a[9]) b.d = a[9];
    if (b.t == 'abs')
        for (let i = 0; i < (a[6] || []).length; i += 6) b.slots.push(a[6].slice(i, i + 6));
    else
        for (let i = 0; i < a[6].length; i += 4) b.slots.push(a[6].slice(i, i + 4));
    return b
};
// Compact, self-contained binary format (LGS) because a JSON was clearly NOT short enough
const TYPE_ID = { io: 0, not: 1, and: 2, abs: 3 },
    ID_TYPE = ['io', 'not', 'and', 'abs'];
const MAX_IMPORT_CHARS = 1000000, MAX_IMPORT_ITEMS = 20000, MAX_IMPORT_DEFS = 256;
const makeData = () => ({
    v: 1,
    g: [G.x0, G.y0, G.x1, G.y1],
    d: Object.entries(defs).map(([k, d]) => [k, d.name, d.color, d.ports.map(p => [p.id, pinName(p), p.k]), d.blocks.map(sb)]),
    b: blocks.map(sb)
});

// LGS layout: header 'L','G',3 -> grid bounds -> definition keys -> each definition (name, colour, pins, blocks) -> root blocks
// Result is URL-friendly base64 since FOR SOME REASON just sharing strings wasnt good
function encodeCompact(o) {
    const a = [76, 71, 3],
        te = new TextEncoder(),
        keys = o.d.map(d => d[0]),
        keyId = new Map(keys.map((k, i) => [k, i]));
    const u = n => {
        if (!Number.isSafeInteger(n) || n < 0) throw Error('Invalid unsigned integer');
        do {
            let b = n % 128;
            n = Math.floor(n / 128);
            a.push(b | (n ? 128 : 0))
        } while (n)
    };
    const si = n => u(n >= 0 ? 2 * n : -2 * n - 1);
    const st = s => {
        const b = te.encode(String(s ?? ''));
        u(b.length);
        for (const v of b) a.push(v)
    };
    const block = b => {
        u(b[0]);
        const t = TYPE_ID[b[1]];
        if (t === undefined) throw Error('Unknown block type');
        a.push(t);
        si(b[2]);
        si(b[3]);
        u(b[4]);
        u(b[5]);
        u(b[7] ? 1 : 0);
        st(b[8] || '');
        if (b[1] === 'abs') {
            const k = keyId.get(b[9]);
            if (k === undefined) throw Error('Missing abstract block definition');
            u(k)
        }
        const q = b[6] || [],
            stride = b[1] === 'abs' ? 6 : 4;
        if (q.length % stride) throw Error('Invalid slot data');
        u(q.length / stride);
        for (let i = 0; i < q.length; i += stride) {
            const x = q[i] - b[2],
                y = q[i + 1] - b[3];
            if (x < 0 || y < 0 || x >= b[4] || y >= b[5]) throw Error('Slot outside block');
            u(y * b[4] + x);
            a.push((q[i + 2] & 3) | ((q[i + 3] & 3) << 2));
            if (b[1] === 'abs') {
                st(q[i + 4]);
                st(q[i + 5])
            }
        }
    };
    o.g.forEach(si);
    u(o.d.length);
    for (const k of keys) st(k);
    for (const d of o.d) {
        st(d[1]);
        st(d[2]);
        u(d[3].length);
        for (const p of d[3]) {
            u(p[0]);
            st(p[1]);
            u(p[2])
        }
        u(d[4].length);
        for (const b of d[4]) block(b)
    }
    u(o.b.length);
    for (const b of o.b) block(b);
    const bytes = new Uint8Array(a);
    let bin = '';
    for (let i = 0; i < bytes.length; i += 0x8000) bin += String.fromCharCode(...bytes.subarray(i, i + 0x8000));
    return 'LGS_' + btoa(bin).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}

 // Yes, the indent here is off by exactly one tab AND one space
 // My formatter refused to touch it
 // I refused to fix it manually out of sheer spite
 // We are locked in a standoff
 // It works, move on
function decodeCompact(s) {
         if (!s.startsWith('LGS_')) throw Error('Unsupported format');
         const b64 = s.slice(4).replace(/-/g, '+').replace(/_/g, '/');
         if (!/^[A-Za-z0-9+/]*$/.test(b64)) throw Error('Invalid compact string');
         const bin = atob(b64 + '='.repeat((4 - b64.length % 4) % 4)),
             bytes = new Uint8Array(bin.length);
         for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
         let p = 0;
         const td = new TextDecoder('utf-8', {
             fatal: true
         });
         const byte = () => {
             if (p >= bytes.length) throw Error('Unexpected end of compact data');
             return bytes[p++]
         };
         if (byte() !== 76 || byte() !== 71 || byte() !== 3) throw Error('Unsupported compact format');
         const u = () => {
             let n = 0,
                 m = 1;
             for (let i = 0; i < 8; i++) {
                 const b = byte();
                 n += (b & 127) * m;
                 if (!(b & 128)) {
                     if (!Number.isSafeInteger(n)) throw Error('Integer too large');
                     return n
                 }
                 m *= 128
             }
             throw Error('Invalid integer')
         };
         const si = () => {
             const n = u();
             return n % 2 ? -(n + 1) / 2 : n / 2
         };
         const st = () => {
             const n = u();
             if (n > bytes.length - p) throw Error('Invalid string length');
             const v = td.decode(bytes.subarray(p, p + n));
             p += n;
             return v
         };
         const count = () => {
             const n = u();
             if (n > MAX_IMPORT_ITEMS) throw Error('Item limit exceeded');
             return n
         };
         const g = [si(), si(), si(), si()],
             nd = count(),
             keys = [];
         for (let i = 0; i < nd; i++) keys.push(st());
         const block = () => {
             const id = u(),
                 type = byte(),
                 t = ID_TYPE[type];
             if (!t) throw Error('Invalid block type');
             const x = si(),
                 y = si(),
                 w = u(),
                 h = u(),
                 v = u(),
                 label = st();
             if (!w || !h || w > 64 || h > 64 || v > 1) throw Error('Invalid block');
             let dk = 0;
             if (t === 'abs') {
                 dk = u();
                 if (dk >= keys.length) throw Error('Missing abstract definition')
             }
             const ns = count(),
                 slots = [];
             for (let i = 0; i < ns; i++) {
                 const idx = u(),
                     z = byte();
                 if (idx >= w * h || z > 11) throw Error('Invalid slot');
                 slots.push(x + idx % w, y + Math.floor(idx / w), z & 3, z >> 2);
                 if (t === 'abs') slots.push(st(), st());
             }
             return [id, t, x, y, w, h, slots, v, label, t === 'abs' ? keys[dk] : 0];
         };
         const d = [];
         for (const k of keys) {
             const name = st(),
                 color = st(),
                 np = count(),
                 ports = [];
             for (let i = 0; i < np; i++) ports.push([u(), st(), u()]);
             const nb = count(),
                 blocks = [];
             for (let i = 0; i < nb; i++) blocks.push(block());
             d.push([k, name, color, ports, blocks])
         }
         const nb = count(),
             blocks = [];
         for (let i = 0; i < nb; i++) blocks.push(block());
         if (p !== bytes.length) throw Error('Extra data');
         return {
             v: 1,
             g,
             d,
             b: blocks
         };
}
const ser = () => encodeCompact(makeData());

// Grow the grid (never shrink it) so it holds every block, imports can ask for weird sizes
function fitG(g) {
    G = g ? {
        x0: g[0],
        y0: g[1],
        x1: g[2],
        y1: g[3]
    } : {
        x0: 0,
        y0: 0,
        x1: 12,
        y1: 12
    };
    blocks.forEach(b => {
        G.x0 = Math.min(G.x0, b.x);
        G.y0 = Math.min(G.y0, b.y);
        G.x1 = Math.max(G.x1, b.x + b.w);
        G.y1 = Math.max(G.y1, b.y + b.h)
    })
}

// Imported text is untrusted, so we check EVERYTHING: numbers, string lengths, overlaps, definition cycles
// This is the only reason why pasting garbage can't break your board. So thank me for it.
function validateImportData(o) {
    const fail = () => { throw new Error('INVALID_IMPORT') };
    const isInt = Number.isSafeInteger;
    const isCoord = n => isInt(n) && Math.abs(n) <= 1_000_000;

    if (!o || typeof o !== 'object' || (o.v !== undefined && o.v !== 1) ||
        !Array.isArray(o.g) || o.g.length !== 4 ||
        !Array.isArray(o.d) || !Array.isArray(o.b)) fail();

    const [gx0, gy0, gx1, gy1] = o.g;
    if (![gx0, gy0, gx1, gy1].every(isCoord) ||
        gx1 <= gx0 || gy1 <= gy0 ||
        gx1 - gx0 > MAXN || gy1 - gy0 > MAXN ||
        o.d.length > MAX_IMPORT_DEFS) fail();

    const keys = new Set();
    let totalItems = 0;

    for (const d of o.d) {
        if (!Array.isArray(d) || d.length < 5) fail();
        const [key, name, color, ports, innerBlocks] = d;
        if (typeof key !== 'string' || !key || key.length > 128 || keys.has(key) ||
            typeof name !== 'string' || name.length > 128 ||
            typeof color !== 'string' || color.length > 64 ||
            !Array.isArray(ports) || !Array.isArray(innerBlocks)) fail();
        keys.add(key);
        totalItems += ports.length;
        if (totalItems > MAX_IMPORT_ITEMS) fail();
        for (const p of ports) {
            if (!Array.isArray(p) || p.length < 3 ||
                !isInt(p[0]) || p[0] < 0 ||
                typeof p[1] !== 'string' || p[1].length > 128 ||
                (p[2] !== 1 && p[2] !== 2)) fail();
        }
    }

    const graph = new Map(o.d.map(d => [d[0], []]));
    const lists = [
        { items: o.b, bounds: o.g, owner: null },
        ...o.d.map(d => ({ items: d[4], bounds: [0, 0, 12, 12], owner: d[0] }))
    ];
    let totalSlots = 0;

    for (const entry of lists) {
        if (!Array.isArray(entry.items)) fail();
        totalItems += entry.items.length;
        if (totalItems > MAX_IMPORT_ITEMS) fail();

        let [x0, y0, x1, y1] = entry.bounds;
        const ids = new Set();
        const occupied = new Set();
        let area = 0;

        for (const a of entry.items) {
            if (!Array.isArray(a) || a.length < 9) fail();
            const [id, t, x, y, w, h, rawSlots, v, label, defKey] = a;
            if (!isInt(id) || id < 0 || ids.has(id) ||
                !['io', 'not', 'and', 'abs'].includes(t) ||
                !isCoord(x) || !isCoord(y) ||
                !isInt(w) || !isInt(h) || w < 1 || h < 1 || w > MAXN || h > MAXN ||
                !isCoord(x + w) || !isCoord(y + h) ||
                (v !== 0 && v !== 1) ||
                (label != null && (typeof label !== 'string' || label.length > 512))) fail();
            ids.add(id);

            if (t === 'abs' && (typeof defKey !== 'string' || !keys.has(defKey))) fail();

            const slots = rawSlots == null && t === 'abs' ? [] : rawSlots;
            const stride = t === 'abs' ? 6 : 4;
            if (!Array.isArray(slots) || slots.length % stride !== 0 ||
                slots.length / stride > (t === 'abs' ? 2 * (w + h) : 4 * w * h)) fail();

            totalSlots += slots.length / stride;
            if (totalSlots > MAX_IMPORT_ITEMS * 8) fail();
            const slotKeys = new Set();
            for (let i = 0; i < slots.length; i += stride) {
                const sx = slots[i], sy = slots[i + 1], dir = slots[i + 2], kind = slots[i + 3];
                if (!isCoord(sx) || !isCoord(sy) ||
                    sx < x || sx >= x + w || sy < y || sy >= y + h ||
                    !isInt(dir) || dir < 0 || dir > 3 ||
                    (kind !== 1 && kind !== 2)) fail();
                const sk = sx + ',' + sy + ',' + dir;
                if (slotKeys.has(sk)) fail();
                slotKeys.add(sk);
                if (t === 'abs' &&
                    (typeof slots[i + 4] !== 'string' || slots[i + 4].length > 128 ||
                        typeof slots[i + 5] !== 'string' || slots[i + 5].length > 256)) fail();
            }

            if (t === 'abs' && entry.owner !== null) graph.get(entry.owner).push(defKey);

            area += w * h;
            if (area > MAXN * MAXN) fail();
            for (let dx = 0; dx < w; dx++) {
                for (let dy = 0; dy < h; dy++) {
                    const cell = (x + dx) + ',' + (y + dy);
                    if (occupied.has(cell)) fail();
                    occupied.add(cell);
                }
            }

            x0 = Math.min(x0, x);
            y0 = Math.min(y0, y);
            x1 = Math.max(x1, x + w);
            y1 = Math.max(y1, y + h);
        }

        if (x1 - x0 > MAXN || y1 - y0 > MAXN) fail();
    }

    // Recursive abstract definitions would recurse forever during simulation
    const state = new Map();
    const visit = (key, depth) => {
        if (depth > 64 || state.get(key) === 1) fail();
        if (state.get(key) === 2) return;
        state.set(key, 1);
        for (const child of graph.get(key)) visit(child, depth + 1);
        state.set(key, 2);
    };
    for (const key of keys) visit(key, 0);
}

// Imports an LGS_ board string
// even on one TINY failure, the previous board is restored and INVALID_IMPORT is thrown
function load(str) {
    if (typeof str !== 'string' || !str.trim()) throw new Error('EMPTY_IMPORT');
    if (str.length > MAX_IMPORT_CHARS) throw new Error('IMPORT_TOO_LARGE');
    str = str.trim();

    const o = decodeCompact(str);
    validateImportData(o);

    // Keep the current board intact if anything unexpected fails during application
    const previous = {
        G, defs, blocks, nid, sel, nodes, cmap, H, cyclicNodes, topoOrder
    };
    let previousSaved = null, canRestoreSaved = false;
    try {
        previousSaved = localStorage.getItem('lgs');
        canRestoreSaved = true;
    } catch (e) {}

    try {
        defs = {};
        for (const d of o.d) {
            defs[d[0]] = {
                name: d[1],
                color: d[2],
                ports: d[3].map(p => ({
                    id: p[0],
                    pin: String(p[1] ?? ''),
                    label: String(p[1] ?? ''),
                    k: p[2]
                })),
                blocks: []
            };
        }

        let m = 0;
        for (const d of o.d) {
            defs[d[0]].blocks = d[4].map(ub);
            d[4].forEach(a => m = Math.max(m, a[0]));
        }
        blocks = o.b.map(ub);
        blocks.forEach(b => m = Math.max(m, b.id));
        nid = m + 1;
        sel = null;
        nodes = [];
        fitG(o.g);
        commit();
        pal();
    } catch (e) {
        G = previous.G;
        defs = previous.defs;
        blocks = previous.blocks;
        nid = previous.nid;
        sel = previous.sel;
        nodes = previous.nodes;
        cmap = previous.cmap;
        H = previous.H;
        cyclicNodes = previous.cyclicNodes;
        topoOrder = previous.topoOrder;
        if (canRestoreSaved) {
            try {
                if (previousSaved === null) localStorage.removeItem('lgs');
                else localStorage.setItem('lgs', previousSaved);
            } catch (x) {}
        }
        try { panel(); pal(); } catch (x) {}
        dirty = 1;
        throw new Error('INVALID_IMPORT');
    }
}

function save() {
    if (editingDefKey) return;
    try {
        localStorage.setItem('lgs', ser())
    } catch (e) {}
}
const saveSet = () => {
    try {
        localStorage.setItem('lgs_s', JSON.stringify({
            speed
        }))
    } catch (e) {}
};

// The "something changed" button
// Rebuild the sim, save, refresh the panel, push undo history
// Call it after any edit to blocks/defs/G
// Forget it, and the screen lies to your face
function commit() {
    rebuild();
    save();
    panel();
    dirty = 1;
    pushHistory()
}

/*
5. Undo/Redo
Whole-board JSON snapshots! Not fast, never been a problem, so it stays that way
If any of you has a better idea, i will "take it into consideration" (aka. throw it to the recycle bin)
*/

const MAX_HIST = 100;
const histSnapshot = () => JSON.stringify({ G, defs, blocks, nid });

function pushHistory() {
    if (histBusy) return;
    const s = histSnapshot();
    if (histIdx >= 0 && hist[histIdx] === s) {
        updateUndoButtons();
        return
    }
    hist = hist.slice(0, histIdx + 1);
    hist.push(s);
    if (hist.length > MAX_HIST) hist.shift();
    else histIdx++;
    histIdx = Math.min(histIdx, hist.length - 1);
    updateUndoButtons()
}

function applySnapshot(s) {
    const o = JSON.parse(s);
    G = o.G;
    defs = o.defs;
    blocks = o.blocks;
    nid = o.nid;
    sel = null;
    histBusy = true;
    try {
        rebuild();
        save();
        panel();
        pal()
    } finally {
        histBusy = false
    }
    dirty = 1;
    updateUndoButtons()
}

function undo() {
    if (histIdx <= 0) return;
    histIdx--;
    applySnapshot(hist[histIdx])
}

function redo() {
    if (histIdx >= hist.length - 1) return;
    histIdx++;
    applySnapshot(hist[histIdx])
}

function updateUndoButtons() {
    const u = $('#bUndo'),
        r = $('#bRedo');
    if (u) u.disabled = histIdx <= 0;
    if (r) r.disabled = histIdx >= hist.length - 1
}
$('#bUndo').onclick = undo;
$('#bRedo').onclick = redo;
document.addEventListener('keydown', e => {
    const tag = (e.target && e.target.tagName) || '';
    if (tag === 'INPUT' || tag === 'TEXTAREA') return;
    if (!(e.ctrlKey || e.metaKey)) return;
    const k = e.key.toLowerCase();
    if (k === 'z' && !e.shiftKey) {
        e.preventDefault();
        undo()
    } else if (k === 'y' || (k === 'z' && e.shiftKey)) {
        e.preventDefault();
        redo()
    }
});

/*
6. Rendering
Everything on the canvas with draw() as the entry point
*/

// Reading CSS variables every frame is slow, so we only peek once a second
// Flip the theme and the canvas takes up to a second to notice and i've decided thats charming
let Cc, Ct = 0;

function C() {
    const t = performance.now();
    if (!Cc || t - Ct > 1000) {
        Cc = C0();
        Ct = t
    }
    return Cc
}

function C0() {
    const c = getComputedStyle(document.documentElement);
    return {
        bg: c.getPropertyValue('--bg'),
        card: c.getPropertyValue('--card'),
        grid: c.getPropertyValue('--grid'),
        acc: c.getPropertyValue('--acc'),
        mut: c.getPropertyValue('--mut')
    }
}

// Rounded-rectangle path
function rr(x, y, w, h, r) {
    const c = ctx;
    c.beginPath();
    c.moveTo(x + r, y);
    c.arcTo(x + w, y, x + w, y + h, r);
    c.arcTo(x + w, y + h, x, y + h, r);
    c.arcTo(x, y + h, x, y, r);
    c.arcTo(x, y, x + w, y, r);
    c.closePath()
}

// One arrow head
// Colour: explicit > yellow if the signal is 1 > grey
// Red marks an invalid pin
// The vertex maths looks like witchcraft
// it's a triangle, rotated to face d
// Not rocket science
function tri(px, py, d, t, v, color = null) {
    const c = ctx;
    c.beginPath();
    c.moveTo(px + d[0] * t, py + d[1] * t);
    c.lineTo(px - d[0] * t - d[1] * t, py - d[1] * t + d[0] * t);
    c.lineTo(px - d[0] * t + d[1] * t, py - d[1] * t - d[0] * t);
    c.closePath();
    c.fillStyle = color || (v ? ON : '#8a8d94');
    c.fill();
    c.lineWidth = 1;
    c.strokeStyle = '#26282c';
    c.stroke()
}

// Body, label and arrows of a single block (skipped when off-screen)
function drawBlock(b) {
    const c = ctx,
        s = cam.s,
        x = cam.x + b.x * s,
        y = cam.y + b.y * s,
        w = b.w * s,
        h = b.h * s,
        m = s * .05,
        hd = H[b.id],
        lit = hd && hd.n && hd.n.v;
    if (x + w < 0 || y + h < 0 || x > cv.clientWidth || y > cv.clientHeight) return;
    const light = b.t == 'io' && b.slots.some(q => q[3] == 1) && !b.slots.some(q => q[3] == 2);
    rr(x + m, y + m, w - 2 * m, h - 2 * m, s * .1);
    c.fillStyle = b.t == 'abs' ? defs[b.d].color : COL[b.t];
    c.fill();
    c.lineWidth = lit && !light && b.t != 'io' ? 3 : 1.5;
    c.strokeStyle = lit && !light && b.t != 'io' ? ON : '#2a2c30';
    c.stroke();
    c.fillStyle = '#1b1c1f';
    c.textAlign = 'center';
    c.textBaseline = 'middle';
    if (b.t == 'io') {
        if (light) {
            c.beginPath();
            c.arc(x + w / 2, y + h / 2, s * .26, 0, 7);
            c.fillStyle = lit ? ON : '#b9bbc0';
            c.fill();
            c.stroke()
        } else {
            c.font = `600 ${s*.36}px system-ui`;
            c.fillText(lit ? 1 : 0, x + w / 2, y + h / 2)
        }
        if (showLab && b.label) {
            c.fillStyle = '#1b1c1f';
            c.font = `${s*.15}px system-ui`;
            c.fillText(b.label, x + w / 2, y + h - s * .13)
        }
    } else {
        c.font = `600 ${s*.2}px system-ui`;
        c.fillText(b.t == 'abs' ? defs[b.d].name : b.t.toUpperCase(), x + w / 2, y + h / 2)
    }
    for (const q of b.slots) {
        const dv = D[q[2]],
            v = q[3] == 2 ? hd && hd.out(q) && hd.out(q).v : wire.get(q) && wire.get(q).v,
            dir = q[3] == 1 ? [-dv[0], -dv[1]] : dv;
        tri(cam.x + (q[0] + .5 + dv[0] * .5) * s - dv[0] * s * .17, cam.y + (q[1] + .5 + dv[1] * .5) * s - dv[1] * s * .17, dir, s * .09, v, pinInvalid(b, q) ? '#e53935' : null);
        if (b.t == 'abs' && showLab) {
            c.fillStyle = '#1b1c1f';
            c.font = `${s*.14}px system-ui`;
            const L = String(q[5] ?? '~') === '~' ? String(q[4] ?? '') : String(q[5] ?? ''),
                px = cam.x + (q[0] + .5) * s,
                py = cam.y + (q[1] + .5) * s;
            if (q[2] == 3) {
                c.textAlign = 'left';
                c.fillText(L, px - s * .2, py)
            } else if (q[2] == 1) {
                c.textAlign = 'right';
                c.fillText(L, px + s * .2, py)
            } else {
                c.textAlign = 'center';
                c.fillText(L, px, py + (q[2] == 0 ? s * .3 : -s * .3))
            }
        }
    }
}
// Where the "+" tile for side d goes
// It hugs the board edge but slides along to stay on screen, which is the sort of nicety nobody notices until it's missing
const expR = d => {
    const s = cam.s,
        z = s * .7,
        W = cv.clientWidth,
        Hh = cv.clientHeight,
        l = cam.x + G.x0 * s,
        r = cam.x + G.x1 * s,
        t = cam.y + G.y0 * s,
        b = cam.y + G.y1 * s,
        vx = Math.min(Math.max(W / 2, l + z / 2), r - z / 2),
        vy = Math.min(Math.max(Hh / 2, t + z / 2), b - z / 2);
    return d == 0 ? [vx - z / 2, t - z - s * .15, z] : d == 2 ? [vx - z / 2, b + s * .15, z] : d == 3 ? [l - z - s * .15, vy - z / 2, z] : [r + s * .15, vy - z / 2, z]
};
const expTap = (px, py) => {
    for (let d = 0; d < 4; d++) {
        const r = expR(d);
        if (px >= r[0] && px <= r[0] + r[2] && py >= r[1] && py <= r[1] + r[2]) {
            expand(d);
            return 1
        }
    }
    return 0
};

function expand(d) {
    if ((d % 2 ? G.x1 - G.x0 : G.y1 - G.y0) >= MAXN) {
        toast('Max ' + MAXN + ' cells');
        return
    }
    if (d == 0) G.y0--;
    else if (d == 1) G.x1++;
    else if (d == 2) G.y1++;
    else G.x0--;
    commit()
}

function draw() {
    dirty = 0;
    const c = ctx,
        s = cam.s,
        W = cv.clientWidth,
        Hh = cv.clientHeight,
        k = C();
    c.setTransform(dpr, 0, 0, dpr, 0, 0);
    c.fillStyle = k.bg;
    c.fillRect(0, 0, W, Hh);
    c.fillStyle = k.card;
    const gx = cam.x + G.x0 * s,
        gy = cam.y + G.y0 * s,
        gw = (G.x1 - G.x0) * s,
        gh = (G.y1 - G.y0) * s;
    c.fillRect(gx, gy, gw, gh);
    c.strokeStyle = k.grid;
    c.lineWidth = 1;
    c.beginPath();
    for (let i = 0; i <= G.x1 - G.x0; i++) {
        const x = Math.round(gx + i * s) + .5;
        c.moveTo(x, gy);
        c.lineTo(x, gy + gh)
    }
    for (let i = 0; i <= G.y1 - G.y0; i++) {
        const y = Math.round(gy + i * s) + .5;
        c.moveTo(gx, y);
        c.lineTo(gx + gw, y)
    }
    c.stroke();
    blocks.forEach(drawBlock);
    
    // Tutorial visual overlay for specific grid targets
    const tutCells = tutHighlightCells();
    if (tutCells) {
        c.fillStyle = 'rgba(255, 213, 74, 0.2)';
        c.strokeStyle = ON;
        c.lineWidth = 2;
        c.setLineDash([4, 4]);
        c.lineDashOffset = -(performance.now() / 150);
        for (const [cx, cy] of tutCells) {
            const rx = cam.x + cx * s, ry = cam.y + cy * s;
            c.fillRect(rx, ry, s, s);
            c.strokeRect(rx, ry, s, s);
        }
        c.setLineDash([]);
        dirty = 1;
    }

    if (mode == 'build')
        for (let d = 0; d < 4; d++) {
            const r = expR(d);
            rr(r[0], r[1], r[2], r[2], s * .15);
            c.fillStyle = k.grid;
            c.fill();
            c.fillStyle = k.acc;
            c.font = `600 ${s*.5}px system-ui`;
            c.textAlign = 'center';
            c.textBaseline = 'middle';
            c.fillText('+', r[0] + r[2] / 2, r[1] + r[2] / 2)
        }
    if (sel && mode == 'build') {
        const b = sel;
        rr(cam.x + b.x * s, cam.y + b.y * s, b.w * s, b.h * s, s * .1);
        c.setLineDash([6, 4]);
        c.lineWidth = 2;
        c.strokeStyle = k.acc;
        c.stroke();
        c.setLineDash([]);
        if (b.t != 'abs')
            for (let i = 0; i < b.w; i++)
                for (let j = 0; j < b.h; j++)
                    for (let d = 0; d < 4; d++) {
                        const x = b.x + i,
                            y = b.y + j,
                            nb = cmap[(x + D[d][0]) + ',' + (y + D[d][1])];
                        if (nb !== b && !b.slots.some(q => q[0] == x && q[1] == y && q[2] == d)) {
                            c.beginPath();
                            c.arc(cam.x + (x + .5 + D[d][0] * .4) * s, cam.y + (y + .5 + D[d][1] * .4) * s, s * .06, 0, 7);
                            c.strokeStyle = k.acc;
                            c.lineWidth = 1.5;
                            c.stroke()
                        }
                    }
    }
}
/*
7. Board editing
Everything a tap can do in build mode: select, add/cycle arrows, resize, place, delete.
*/

// Does block b fit on the board without hitting anything (other than "ig", usually itself)?
function fits(b, ig) {
    for (let i = 0; i < b.w; i++)
        for (let j = 0; j < b.h; j++) {
            const x = b.x + i,
                y = b.y + j,
                o = cmap[x + ',' + y];
            if (!inB(x, y) || (o && o !== ig)) return 0
        }
    return 1
}

// Tapping an edge cycles its arrow: none -> input -> output -> none
// I/O and NOT may only have one input, so for them a second "input" skips straight to "output"
function cycle(b, x, y, d) {
    const i = b.slots.findIndex(q => q[0] == x && q[1] == y && q[2] == d),
        lim = b.t == 'io' || b.t == 'not',
        ins = b.slots.filter(q => q[3] == 1).length;
    let k = ((i < 0 ? 0 : b.slots[i][3]) + 1) % 3;
    if (k == 1 && lim && ins >= 1) k = 2;
    let old = i >= 0 ? b.slots[i] : null;
    if (i >= 0) b.slots.splice(i, 1);
    if (k) {
        if (b.t === 'abs') {
            const dfn = defs[b.d],
                pin = old ? String(old[4] ?? '') : (dfn?.ports?.find(p => p.k === k) ? pinName(dfn.ports.find(p => p.k === k)) : '');
            const label = old ? String(old[5] ?? '~') : '~';
            b.slots.push([x, y, d, k, pin, label])
        } else b.slots.push([x, y, d, k])
    }
    commit()
}

// Grow/shrink a block by (dw, dh) if there's room. Plain blocks drop any arrows that end up
// facing their own insides; abstract blocks simply re-run layoutAbs
// That one-line filter below is doing a LOT
// Read it twice
// Please
function resize(b, dw, dh) {
    const o = {
        ...b,
        w: Math.max(1, b.w + dw),
        h: Math.max(1, b.h + dh)
    };
    if (!fits(o, b)) {
        toast('Not enough room');
        return
    }
    if (b.t == 'abs') {
        b.w = o.w;
        b.h = o.h;
        layoutAbs(b, 1);
        commit();
        return
    }
    b.w = o.w;
    b.h = o.h;
    b.slots = b.slots.filter(q => q[0] < b.x + b.w && q[1] < b.y + b.h && !(cellMap([b])[(q[0] + D[q[2]][0]) + ',' + (q[1] + D[q[2]][1])]));
    commit()
}

// Single entry point for every tap on the board, routed by state:
// truth-table mode -> show a table | view mode -> flip a switch | build mode -> expand tile/select/cycle an arrow/place the current tool
function tap(px, py) {
    const wx = (px - cam.x) / cam.s,
            wy = (py - cam.y) / cam.s,
            cx = Math.floor(wx),
            cy = Math.floor(wy);

    if (probing) {
        if (inB(cx, cy)) {
            const b = cmap[cx + ',' + cy];
            if (b && b.t === 'abs') showTruthTable(b);
            else if (b) toast('Tap an abstract block to see its truth table');
        }
        return;
    }

    if (mode == 'build' && expTap(px, py)) return;
    if (!inB(cx, cy)) return;
    const b = cmap[cx + ',' + cy];
    
    if (mode == 'view') {
        if (b && b.t == 'io' && !b.slots.some(q => q[3] == 1)) {
            b.v ^= 1;
            H[b.id].n.v = b.v;
            save();
            dirty = 1;
        }
        return;
    }
    if (b) {
        if (b === sel || b.t === 'abs') {
            const fx = wx - cx,
                fy = wy - cy,
                ds = [fy, 1 - fx, 1 - fy, fx];
            let d = 0;
            ds.forEach((v, i) => { if (v < ds[d]) d = i });
            if (ds[d] < .3 && cmap[(cx + D[d][0]) + ',' + (cy + D[d][1])] !== b) {
                sel = b;
                cycle(b, cx, cy, d);
                return;
            }
        }
        sel = b;
        panel();
        dirty = 1;
        return;
    }
    if (tool) {
        if (defs[tool] && editingDefKey && dependsOn(tool, editingDefKey)) return;
        const nb = defs[tool] ? mk('abs', cx, cy, { d: tool }) : mk(tool, cx, cy);
        if (!fits(nb)) {
            toast('Not enough room');
            return;
        }
        blocks.push(nb);
        sel = nb;
        commit();
    } else {
        sel = null;
        panel();
        dirty = 1;
    }
}

// The bottom sheet for the selected block
// It's rebuilt from a template string every single time which feels wrong and has never once caused a problem, so deal with it
function panel() {
    const el = $('#sheet'),
        b = sel;
    if (!b || mode != 'build') {
        el.hidden = 1;
        return
    }
    el.hidden = 0;
    const rs = b.t == 'not' || b.t == 'and' || b.t == 'abs';
    el.innerHTML = `<b>${esc(b.t=='abs'?defs[b.d].name:b.t=='io'?'I/O':b.t.toUpperCase())}</b>` +
        (b.t == 'io' ? `<input id="lab" type="text" size="9" value="${esc(b.label)}">` : '') +
        (rs ? `<span>W <button data-r="-1,0">−</button> ${b.w} <button data-r="1,0">+</button> &nbsp;H <button data-r="0,-1">−</button> ${b.h} <button data-r="0,1">+</button></span>` : '') +
        `<button id="del">Delete</button>` +
        (b.t === 'abs' && !editingDefKey ? '<button id="editDef">Edit definition</button>' : '')
}
$('#sheet').onclick = e => {
    const t = e.target;
    if (t.id == 'del') {
        blocks = blocks.filter(b => b !== sel);
        sel = null;
        commit()
    } else if (t.id === 'editDef') {
        beginEditDefinition(sel.d)
    } else if (t.dataset.r) {
        const r = t.dataset.r.split(',').map(Number);
        resize(sel, r[0], r[1])
    }
};
$('#sheet').oninput = e => {
    if (e.target.id == 'lab') {
        sel.label = e.target.value;
        save();
        dirty = 1
    }
};

// Does definition `key` contain `target`, directly or deeper? Used to forbid recursive definitions.
function dependsOn(key, target, seen = new Set()) {
    if (key === target) return true;
    if (seen.has(key)) return false;
    seen.add(key);
    const d = defs[key];
    return !!d?.blocks?.some(b => b.t === 'abs' && dependsOn(b.d, target, new Set(seen)))
}

/*
8. Pallete, modes, toasts and example boards
Tool bar, Build/View switch, the Aa toggle, little pop-ups, and the canned example boards (small section, big dreams)
*/

// Rebuilds the palette buttons (predefined+your abstract blocks)
function pal() {
    $('#pal').innerHTML = [
            ['io', 'I/O', '#f4f4f4'],
            ['not', 'NOT', COL.not],
            ['and', 'AND', COL.and], ...Object.entries(defs).filter(([k]) => !editingDefKey || !dependsOn(k, editingDefKey)).map(([k, d]) => [k, d.name, d.color])
        ]
        .map(([k, n, c]) => `<button data-t="${k}" class="${tool==k?'on':''}"><i style="background:${c}"></i>${esc(n)}</button>`).join('')
}
$('#pal').onclick = e => {
    const t = e.target.closest('button');
    if (t) {
        tool = tool == t.dataset.t ? null : t.dataset.t;
        pal()
    }
};
$('#bMode').onclick = e => {
    if (editingDefKey) {
        openSaveDefinitionDialog();
        return
    }
    mode = mode == 'view' ? 'build' : 'view';
    tool = null;
    if (mode == 'view') sel = null;
    document.body.dataset.m = mode;
    e.target.classList.toggle('on', mode == 'build');
    pal();
    panel();
    dirty = 1
};
$('#bLab').onclick = e => {
    showLab = !showLab;
    e.target.classList.toggle('on', showLab);
    dirty = 1
};
let tt;

function toast(m) {
    const t = $('#toast');
    t.textContent = m;
    t.style.opacity = 1;
    clearTimeout(tt);
    tt = setTimeout(() => t.style.opacity = 0, 2600)
}

// Example boards: exported LGS_ strings. To add one, build it, Import / Export -> copy, paste below
const EXAMPLES = {
    or: 'LGS_TEcDAAAYGAIJZG12OHo5N3N4CWRtdjh6YW12cwROQU5EByM4NjViZWIDAQNJTjIBAwNJTjEBBgNPVVQCBQEAAAIBAQADSU4yAQAJAwAAAAEBAANJTjEBAAkEAgIAAQIAAAMABwEHAAkFAQQAAQEAAAIABwAKBgAEAgEBAANPVVQBAAQCT1IHI2EwY2QwMQMQA0lOMQERA0lOMgESA09VVAIGDQMCAgEBAAAAAwAHA0lOMgF-AAQDSU4xAX4ACQNPVVQBfg4BAAIBAQAAAgAJAAQPAQIAAQEAAAIACgAFEAAAAAEBAANJTjEBAAoRAAQAAQEAA0lOMgEACxIABAIBAQADT1VUAQAHCxMDBAICAgAAAQMABwNJTjEBfgIHA0lOMgF-AQkDT1VUAX4UAAICAQEAAAEACRUAAgQBAQAAAQAJFgAIAgEBAAABAAcXAAIIAQEAAAEACRgAAgoBAQAAAQAJGQEECAEBAAACAAcACRoBBAoBAQAAAgAHAAkbAgYIAQIAAAMABwEHAAkcAQgIAQEAAAIABwAJHgAKCAEBAAABAAc',
    half_adder: 'LGS_TEcDAAAMEAQJZG12NnM4azA1CWRtdjZzYXhzawlkbXY2c2hidnoJZG12NnNqbjg1Ak9SByNhMGNkMDEDAQNJTjEBAgNJTjIBBwNPVVQCBwEAAAABAQADSU4xAQAJAgAAAgEBAANJTjIBAAkDAQIAAQEAAAIABwAJBAECAgEBAAACAAcACQUCBAABAgAAAwAHAAkBBwYBBgABAQAAAgAHAAoHAAYCAQEAA09VVAEABAROQU5EByM1ZjQxY2MDCwNPVVQCDANJTjIBDQNJTjEBBQgCAgABAQAAAwAHAAkABgoBBAABAQAAAgAHAAoLAAQCAQEAA09VVAEABAwAAgIBAQADSU4yAQAIDQAAAAEBAANJTjEBAAkDWE9SByNkMzcwZTADEgNPVVQCEwNJTjIBFANJTjEBBg4DAAACAQAAAQMBCQNPVVQBfgEGA0lOMgF-AAYDSU4xAX4QAwAEAgEAAAADAQkDT1VUAX4BBANJTjIBfgAEA0lOMQF-EQIEAAEDAAADAAcCBwAJEgAGAAEBAANPVVQBAAcTAAICAQEAA0lOMgIACAAKFAAAAgEBAANJTjECAAgACgpIYWxmIEFkZGVyByM0OThjMzgEGQNJTjEBGgNJTjIBGwVDYXJyeQIcA1N1bQIGFwMEBAEBAAACAwAHA0lOMgF-AAQDSU4xAX4ACQNPVVQBfhgCAgIBAQAAAwAFAAYACBkABAIBAQADSU4xAgAKAAsaAAIEAQEAA0lOMgIACAAJGwACAAEBAAVDYXJyeQEABhwABgQBAQADU3VtAQAHDR4DBAICAgAAAwQABwNJTjEBfgIHA0lOMgF-AwkFQ2FycnkBfgEJA1N1bQF-HwACAgEBAAABAAkgAAIEAQEAAAEACSEACAIBAQAAAQAHIgAIBAEBAAABAAckAwQIAgEAAAIDAQkDT1VUAX4ABwNJTjEBfgAGA0lOMgF-JgAICAEBAANTdW0BAAcnAgQMAgEAAAMABwAEAQkoAAgMAQEABUNhcnJ5AQAHKQAECgEBABEgICAgICAgICAgICAgIElOMgIACgAIKgACCgEBABIgICAgICAgICAgICAgICBJTjECAAoACCsAAggBAQAAAgAGAAksAAIMAQEAAAIABAAJ',
    sr_latch: 'LGS_TEcDAAAMEAIJZG12NnM4azA1CWRtdjZ1NmpxZAJPUgcjYTBjZDAxAwEDSU4xAQIDSU4yAQcDT1VUAgcBAAAAAQEAA0lOMQEACQIAAAIBAQADSU4yAQAJAwECAAEBAAACAAcACQQBAgIBAQAAAgAHAAkFAgQAAQIAAAMABwAJAQcGAQYAAQEAAAIABwAKBwAGAgEBAANPVVQBAAQIU1ItTGF0Y2gHI2MyODk2MQMMBVJlc2V0AQ0DU2V0AQ4DT1VUAgYJAwICAQIAAAADAQcDSU4yAX4ACQNPVVQBfgEFA0lOMQF-CgIEAgECAAAEAAcBCwAEAAkLAQQAAQEAAAIABwAKDAACAAEBAQVSZXNldAEACQ0AAAQBAQADU2V0AQAJDgAGAgEBAANPVVQBAAcLEwACBAEBAAABAAkUAAgCAQEAAAEABxYDBAICAgAAAQMABwVSZXNldAF-AgcDU2V0AX4BCQNPVVQBfhcAAgIBAQEAAQAJGAEECAEBAAACAAcACRkAAggBAQEFUmVzZXQBAAkaAgYIAQIAAAQABwEHAQkBChwDBAoBAgAAAAMBBwNJTjIBfgAJA09VVAF-AQUDSU4xAX4dAAYMAQEAAAIABAALHgACDAEBAANTZXQBAAkfAAgKAQEAA09VVAEABw'
};
const EXAMPLE_NAMES = { or: 'OR', half_adder: 'Half adder', sr_latch: 'SR latch' };

function showExamples() {
    modal(`<b>Example boards</b><small style="color:var(--mut)">Loads in place of the current board (use Undo to bring it back).</small><div class="row">` +
        Object.keys(EXAMPLES).map(k => `<button id="ex_${k}">${esc(EXAMPLE_NAMES[k])}</button>`).join('') +
        `</div><div class="row"><button id="cl">Cancel</button></div>`)
}

/*
9. Truth tables
Works for plain logic and for blocks with memory. For memory blocks the table also lists the block's current outputs as inputs, and result columns are marked with + (the next value)
*/

function toggleProbe() {
    probing = !probing;
    const m = $('#bProbeMenu');
    if (m) m.textContent = 'Truth tables: ' + (probing ? 'on' : 'off');
    if (probing) toast('Tap an abstract block for its truth table');
}
let simSeq = 1;

// The engine now handles stateful transitions by locking the output nodes, letting hidden cyclic gates stabilize around them, unlocking, and ticking
function simulateDefTransition(key, assignByName, stateByName, isSequential) {
    const d = defs[key];
    if (!d) return {};
    const savedNodes = nodes, savedCyclic = cyclicNodes, savedTopo = topoOrder;
    try {
        const localNodes = [],
            h = build(d.blocks, localNodes, 'sim' + (simSeq++) + '/');
        nodes = localNodes;
        classify();
        
        if (isSequential) {
            // Neutralize inputs during warmup
            for (const p of d.ports) {
                if (p.k === 1) {
                    const n = h[p.id] && h[p.id].n;
                    if (n) n.v = 0;
                }
            }
            // Lock exposed outputs to force the hidden state to comply
            const outNodes = [];
            for (const p of d.ports) {
                if (p.k === 2) {
                    const n = h[p.id] && h[p.id].n;
                    if (n && n.src) outNodes.push({ n: n.src, v: stateByName[pinName(p)] ? 1 : 0 });
                }
            }
            for(let i = 0; i < 20; i++) {
                outNodes.forEach(o => o.n.v = o.v);
                step();
            }
            outNodes.forEach(o => o.n.v = o.v);
        }
        
        // Apply the actual test inputs
        for (const p of d.ports) {
            if (p.k === 1) {
                const n = h[p.id] && h[p.id].n;
                if (n) n.v = assignByName[pinName(p)] ? 1 : 0;
            }
        }
        
        // 40 ticks to find the stable next state
        for (let i = 0; i < 40; i++) {
            if (!step()) break;
        }
        
        const res = {};
        for (const p of d.ports) {
            if (p.k === 2) {
                const n = h[p.id] && h[p.id].n;
                res[pinName(p)] = n ? n.v : 0;
            }
        }
        return res;
    } finally {
        nodes = savedNodes;
        cyclicNodes = savedCyclic;
        topoOrder = savedTopo;
    }
}

function showTruthTable(b) {
    const d = defs[b.d];
    if (!d) return;
    const ins = d.ports.filter(p => p.k === 1),
            outs = d.ports.filter(p => p.k === 2);
    if (!ins.length && !outs.length) {
        toast('No named pins to tabulate');
        return;
    }

    // Detect if the block has internal loops or is pure feedforward
    let isSequential = false;
    const testNodes = [];
    build(d.blocks, testNodes, 'test_seq/');
    const savedNodes = nodes, savedCyclic = cyclicNodes, savedTopo = topoOrder;
    try {
        nodes = testNodes;
        classify();
        isSequential = cyclicNodes.length > 0;
    } finally {
        nodes = savedNodes;
        cyclicNodes = savedCyclic;
        topoOrder = savedTopo;
    }

    const leftVars = isSequential ? [...ins, ...outs] : [...ins];
    if (leftVars.length > 8) {
        toast('Too many variables for truth table (max 8 combined)');
        return;
    }
    
    const rows = [], totalVars = leftVars.length;
    for (let mask = 0; mask < (1 << totalVars); mask++) {
        const assign = {}, state = {};
        for(let i = 0; i < ins.length; i++) {
            assign[pinName(ins[i])] = (mask >> (totalVars - 1 - i)) & 1;
        }
        if (isSequential) {
            for(let i = 0; i < outs.length; i++) {
                state[pinName(outs[i])] = (mask >> (outs.length - 1 - i)) & 1;
            }
        }
        rows.push({ assign, state, res: simulateDefTransition(b.d, assign, state, isSequential) });
    }
    
    let html = `<b>${esc(d.name)}: truth table</b><div style="overflow:auto;max-height:50vh"><table style="border-collapse:collapse;width:100%;font-size:12px;text-align:center">` +
        '<tr>' + ins.map(p => `<th style="padding:4px;border-bottom:1px solid var(--grid)">${esc(pinName(p))}</th>`).join('') +
        (isSequential ? outs.map(p => `<th style="padding:4px;border-bottom:1px solid var(--grid)">${esc(pinName(p))}</th>`).join('') : '') +
        '<th style="padding:4px;border-bottom:1px solid var(--grid);color:var(--mut)">||</th>' +
        outs.map(p => `<th style="padding:4px;border-bottom:1px solid var(--grid);color:var(--mut)">${esc(pinName(p))}${isSequential?'+':''}</th>`).join('') + '</tr>';
        
    for (const r of rows) {
        html += '<tr>' + ins.map(p => `<td style="padding:4px">${r.assign[pinName(p)]}</td>`).join('') +
            (isSequential ? outs.map(p => `<td style="padding:4px">${r.state[pinName(p)]}</td>`).join('') : '') +
            '<td style="padding:4px;color:var(--mut)">||</td>' +
            outs.map(p => `<td style="padding:4px;font-weight:600">${r.res[pinName(p)] ?? 0}</td>`).join('') + '</tr>';
    }
    html += '</table></div><div class="row"><button id="cl">Close</button></div>';
    modal(html);
}

/*
10. Pin settings and editing abstract blocks
Long-press a pin to rename it and "Edit definition" opens a block's insides on the board
*/

// Finds the pin arrow of an abstract block under the pointer
function arrowAt(px, py) {
    if (mode !== 'build') return null;
    let best = null,
        bd = Infinity;
    for (const b of blocks) {
        if (b.t !== 'abs') continue;
        for (const q of b.slots) {
            const dx = px - (cam.x + (q[0] + .5 + D[q[2]][0] * .33) * cam.s),
                dy = py - (cam.y + (q[1] + .5 + D[q[2]][1] * .33) * cam.s),
                dist = Math.hypot(dx, dy);
            if (dist < Math.max(8, cam.s * .24) && dist < bd) {
                best = {
                    b,
                    q
                };
                bd = dist
            }
        }
    }
    return best
}

function openPinSettings(b, q) {
    pinEdit = {
        id: b.id,
        at: [q[0], q[1], q[2]]
    };
    const pin = String(q[4] ?? ''),
        label = String(q[5] ?? '~');
    modal(`<b>Pin settings</b><label>Pin <input id="pinName" type="text" value="${esc(pin)}"></label><label>Label <input id="pinLabel" type="text" value="${esc(label)}" placeholder="~"></label><small>Use ~ to display the pin name</small><div class="row"><button id="savePin">Save</button><button id="cl">Cancel</button></div>`)
}

function beginEditDefinition(key) {
    if (editingDefKey) {
        return
    }
    const def = defs[key];
    if (!def) return;
    editReturn = {
        G: {
            ...G
        },
        blocks,
        sel,
        tool,
        mode,
        nid
    };
    editingDefKey = key;
    blocks = JSON.parse(JSON.stringify(def.blocks || []));
    sel = null;
    tool = null;
    mode = 'build';
    G = {
        x0: 0,
        y0: 0,
        x1: 12,
        y1: 12
    };
    fitG(G && [G.x0, G.y0, G.x1, G.y1]);
    document.body.dataset.m = 'build';
    $('#bMode').textContent = 'Save block';
    $('#appTitle').textContent = 'Editing: ' + def.name;
    $('#cancelEdit').hidden = false;
    rebuild();
    pal();
    panel();
    dirty = 1;
}

function restoreEditContext() {
    const r = editReturn;
    editingDefKey = null;
    editReturn = null;
    pinEdit = null;
    if (r) {
        G = r.G;
        blocks = r.blocks;
        sel = r.sel;
        tool = r.tool;
        mode = r.mode;
        nid = Math.max(nid, r.nid || nid)
    }
    document.body.dataset.m = mode;
    $('#bMode').textContent = 'Build';
    $('#bMode').classList.toggle('on', mode === 'build');
    $('#appTitle').textContent = 'Logic Gates Sandbox';
    $('#cancelEdit').hidden = true;
    rebuild();
    pal();
    panel();
    save();
    dirty = 1;
    pushHistory()
}

function openSaveDefinitionDialog() {
    if (!editingDefKey) return;
    const d = defs[editingDefKey];
    modal(`<b>Save abstract block</b><label>Name <input id="defName" type="text" value="${esc(d.name)}"></label><label>Colour <input id="defColor" type="color" value="${esc(d.color||'#a0cd01')}"></label><small>Pins defined by labeled I/O cells</small><div class="row"><button id="saveDef">Save changes</button><button id="cl">Continue editing</button></div>`)
}

function finishEditDefinition() {
    const key = editingDefKey,
        d = defs[key];
    if (!key || !d) return;
    for (const b of blocks)
        if (b.t === 'abs' && dependsOn(b.d, key)) {
            return
        }
    const ports = [];
    for (const b of blocks)
        if (b.t === 'io' && String(b.label || '').trim()) ports.push({
            id: b.id,
            pin: String(b.label).trim(),
            label: String(b.label).trim(),
            k: b.slots.some(s => s[3] === 1) ? 2 : 1
        });
    d.blocks = JSON.parse(JSON.stringify(blocks));
    d.ports = ports;
    d.name = $('#defName').value.trim() || d.name;
    d.color = $('#defColor').value;
    restoreEditContext();
}

function cancelEditDefinition() {
    if (!editingDefKey) return;
    restoreEditContext();
}

/*
11. Tutoral
A small state machine
TUT_STEPS is an ordered list; the tutorial sits on one step at a time and moves on when that step's 'advance' condition is met

Step fields:
  m        text shown in the box at the bottom
  advance  "tap" (any tap) or a function that returns true when the player did the thing
  hlUI     CSS selector (or function returning one) of a button/input to make glow
  hlCells  [[x, y], ...] (or function returning that) grid cells to highlight on the canvas
  enter    optional function run once when the step begins (e.g. clear the selected tool)

The lesson, in order: what logic is -> build a NAND (switches, AND, NOT, lamp) -> test it -> pack it into a reusable block -> place it -> read its truth table -> tour the rest
*/

let tutActive = false, tutStep = -1, tutDefCount = 0;

const TAP = "\n(tap anywhere to continue)";
// In build mode a tap on the board can still edit it (a tap near a pin will happily cycle it), so cards shown while building ask for a safe spot
const TAP_AWAY = "\n(tap an empty spot to continue)";

const isSwitch = b => b.t === 'io' && !b.slots.some(s => s[3] === 1);   // I/O with no input arrow
const dropTool = () => { tool = null; pal(); dirty = 1 };               // un-select the tool (it sticks like gum)

// While the menu is closed point at the three dots, once it's open point at the truth-table entry
const menuOrProbe = () => $('#menu').hidden ? '#bMenu' : '#bProbeMenu';
const absCells = () => blocks.filter(b => b.t === 'abs').flatMap(b => {
    const c = [];
    for (let i = 0; i < b.w; i++)
        for (let j = 0; j < b.h; j++) c.push([b.x + i, b.y + j]);
    return c
});

const andWiredCorrectly = () => {
    const g = blocks.find(b => b.t === 'and');
    if (!g) return false;
    const ins = g.slots.filter(s => s[3] === 1);
    return ins.length === 2 && ins.every(s => s[2] === 3) &&
        g.slots.some(s => s[3] === 2 && s[2] === 1 && s[0] === 5 && s[1] === 4)
};

const TUT_STEPS = [
    // What is logic?
    { m: "Welcome to Logic Gates Sandbox!\nHere you'll build tiny digital circuits, the same idea every computer is made of. No experience needed.\nSkip anytime: three dots > Settings > Skip tutorial." + TAP, advance: "tap" },
    { m: "The big idea: every signal here is either 0 (off) or 1 (on).\nA logic gate is a small rule that looks at its input signals and decides its output signal." + TAP, advance: "tap" },
    { m: "NOT gate: flips its input.\n0 becomes 1, and 1 becomes 0." + TAP, advance: "tap" },
    { m: "AND gate: outputs 1 only when ALL of its inputs are 1.\nIf even one input is 0, the output is 0." + TAP, advance: "tap" },
    { m: "OR gate: outputs 1 when ANY input is 1.\nThere's no OR block in the bar, because you can build one yourself from the others. There's a challenge about it at the end." + TAP, advance: "tap" },
    { m: "Put AND and NOT together and you get NAND ('not-and'): its output is 0 only when both inputs are 1.\nFun fact: NAND alone can build every other gate. Let's build one!" + TAP, advance: "tap" },
    { m: "Getting around: drag the board to move it, and pinch (or use the mouse wheel) to zoom." + TAP, advance: "tap" },

    // Build a NAND
    { m: "Tap 'Build' to enter build mode.\nBuild mode is for placing blocks and arrows. View mode (where you are now) is for flipping switches and watching.", advance: () => mode === 'build', hlUI: '#bMode' },
    { m: "Pick the 'I/O' block from the bar at the bottom.\nI/O blocks are your switches (inputs) and lamps (outputs).", advance: () => tool === 'io', hlUI: '#pal button[data-t="io"]' },
    { m: "Tap the two glowing cells to place two I/O blocks.\nThese will be our two input switches.", advance: () => blocks.filter(b => b.t === 'io').length >= 2, hlCells: [[4, 4], [4, 5]] },
    { m: "Blocks talk to each other through arrows on their edges.\nTap a block to select it (dashed outline), then tap close to its right edge to add an arrow. Small circles show where arrows can go.", advance: () => blocks.some(b => b.t === 'io' && b.slots.length > 0), hlCells: [[4, 4], [4, 5]], enter: dropTool },
    { m: "Each tap on the same edge cycles the arrow: pointing IN, then pointing OUT, then gone.\nDo this on both blocks until their arrows point OUT, away from the block. An I/O with an OUT arrow is a switch.", advance: () => blocks.filter(b => b.t === 'io' && b.slots.some(s => s[2] === 1 && s[3] === 2)).length >= 2, hlCells: [[4, 4], [4, 5]] },
    { m: "Now pick the AND block from the bar.", advance: () => tool === 'and', hlUI: '#pal button[data-t="and"]' },
    { m: "Place an AND block on the glowing cell, right next to the switches.", advance: () => blocks.some(b => b.t === 'and' && b.x === 5 && b.y === 4), hlCells: [[5, 4]] },
    { m: "New gates come with some arrows already placed: this AND has inputs on the left and top, and an output on the right.\nTap the + next to H in the bottom panel to make it 2 cells tall.", advance: () => blocks.some(b => b.t === 'and' && b.h >= 2), hlUI: '#sheet button[data-r="0,1"]', enter: dropTool },
    { m: "Give the AND two inputs side by side: tap the top arrow twice to remove it, then tap the bottom-left edge once to add an input there. Keep the output on the right.\n(An input arrow that connects to nothing keeps an AND stuck at 0, so only keep the ones you use.)", advance: andWiredCorrectly, hlCells: [[5, 4], [5, 5]] },
    { m: "Arrows that face each other connect, so your switches now feed the AND.\nNext, pick the NOT block from the bar.", advance: () => tool === 'not', hlUI: '#pal button[data-t="not"]' },
    { m: "Place a NOT on the glowing cell, touching the AND's output.\nIt already has an input arrow on the left and an output arrow on the right.", advance: () => blocks.some(b => b.t === 'not' && b.x === 6 && b.y === 4), hlCells: [[6, 4]] },
    { m: "Almost there! Pick the I/O block again.", advance: () => tool === 'io', hlUI: '#pal button[data-t="io"]' },
    { m: "Place an I/O block next to the NOT, then tap its left edge once so the arrow points IN.\nAn I/O with an IN arrow is a lamp: it lights up when its signal is 1.", advance: () => blocks.some(b => b.t === 'io' && b.x === 7 && b.y === 4 && b.slots.some(s => s[3] === 1)), hlCells: [[7, 4]] },
    { m: "Name your I/O blocks: select one, then type in the box at the bottom (example: IN1, IN2, OUT).\nNames matter: they become the pin names of the block you're about to make.", advance: () => blocks.filter(b => b.t === 'io' && b.label.length > 0).length >= 3, hlUI: '#lab', enter: dropTool },

    // Test it
    { m: "Let's test it! Tap 'Build' again to switch back to View mode.", advance: () => mode === 'view', hlUI: '#bMode' },
    { m: "Tap both switches on the left to turn them from 0 to 1, and watch the lamp.", advance: () => blocks.filter(b => isSwitch(b) && b.v === 1).length >= 2, hlCells: [[4, 4], [4, 5]] },
    { m: "The lamp went dark! Both inputs were 1, so the AND gave 1 and the NOT flipped it to 0.\nTry other combinations: the lamp stays lit unless BOTH switches are on. That's a NAND!\nWhen you're done playing, tap 'Build' to continue.", advance: () => mode === 'build', hlUI: '#bMode' },

    // Make an abstract
    { m: "Now let's pack this circuit into one reusable block.\nClick the three dots.", advance: () => !$('#menu').hidden, hlUI: '#bMenu' },
    { m: "Select 'Abstract board'.", advance: () => !$('#modal').hidden && $('#nm'), hlUI: 'button[data-m="abs"]' },
    { m: "Name this block NAND.\nYour named I/O blocks become its pins: switches turn into inputs, lamps into outputs.", advance: () => $('#nm') && $('#nm').value.toUpperCase() === 'NAND', hlUI: '#nm' },
    { m: "Pick a colour if you like, keep 'Clear board afterwards' ticked, then click 'Create'.", advance: () => Object.keys(defs).length > tutDefCount, hlUI: '#mk' },

    // Use the new block and use truth tables
    { m: "Great! Now you have a NAND gate that you can use!\nIt sits in the bar at the bottom next to I/O, NOT and AND. You can even use blocks inside bigger blocks, which is how whole computers get built from NAND." + TAP, advance: "tap" },
    { m: "Pick your new block from the bar.", advance: () => !!(tool && defs[tool]), hlUI: '#pal button:last-child' },
    { m: "Tap a free cell to place a NAND block.", advance: () => blocks.some(b => b.t === 'abs'), hlCells: [[5, 5]] },
    { m: "Your block shows its pins around the edges, named after your labels.\nSelect it to resize it, delete it, or press 'Edit definition' to open it up and change what's inside. Press and hold a pin arrow to rename it." + TAP_AWAY, advance: "tap", enter: dropTool },
    { m: "Truth tables show what a block does for EVERY combination of inputs.\nTo turn them on, open the three dots and tap 'Truth tables: off'.", advance: () => probing, hlUI: menuOrProbe },
    { m: "Truth tables are on: tapping a block now shows its table.\nTap your NAND block.", advance: () => !$('#modal').hidden, hlCells: absCells },
    { m: "Each row is one combination of inputs (left of ||) and the output it produces (right of ||).\nNAND gives 0 only in the row where both inputs are 1.\nClose the table when you're ready.", advance: () => $('#modal').hidden, hlUI: '#cl' },
    { m: "While truth tables are on, tapping a block only shows its table, so building is paused.\nTurn it off again: three dots, then 'Truth tables: on'.", advance: () => !probing, hlUI: menuOrProbe },

    // The rest
    { m: "Gates can feed their output back into themselves, and that's how circuits remember things.\nThree dots > 'Example boards' loads a half adder (adds two bits) or an SR latch (a 1-bit memory). Loading replaces your board, but Undo brings it back." + TAP_AWAY, advance: "tap" },
    { m: "For memory blocks like the SR latch, the truth table also lists the block's current outputs as inputs, and outputs marked + are the new values." + TAP_AWAY, advance: "tap" },
    { m: "Top bar: the arrows undo and redo your changes, and 'Aa' shows or hides the labels on the board." + TAP_AWAY, advance: "tap" },
    { m: "Settings (three dots) lets you change the simulation speed, Pause, or 'Step once' to watch signals move one tick at a time.\nYou can also grow the board there, or with the + tiles around its edge in build mode." + TAP_AWAY, advance: "tap" },
    { m: "Import / Export (three dots) gives you a code for your whole board, custom blocks included.\nCopy it to share, or paste a code and tap Import." + TAP_AWAY, advance: "tap" },
    { m: "Don't worry, every progress is saved locally on this device.\n'Clear board' empties the board; 'Reset this app' in Settings erases everything." + TAP_AWAY, advance: "tap" },
    { m: "Challenge: build an OR gate out of NANDs. Hint: flip each input first, then NAND the results.\nHave fun!" + TAP_AWAY, advance: "tap" }
];

// Cells to paint a dashed highlight on for the current step
function tutHighlightCells() {
    if (!tutActive || tutStep < 0) return null;
    const st = TUT_STEPS[tutStep];
    if (!st || !st.hlCells) return null;
    return typeof st.hlCells === 'function' ? st.hlCells() : st.hlCells
}

function startTut() {
    if (editingDefKey) cancelEditDefinition();  // leave definition editing first
    if (probing) toggleProbe();                 // truth table mode would block building
    if ($('#menu')) $('#menu').hidden = 1;
    blocks = [];
    sel = null;
    // Start in View mode with no tool. Otherwise "tap Build" might already be true and the whole tutorial feels haunted
    mode = 'view';
    tool = null;
    document.body.dataset.m = 'view';
    $('#bMode').classList.remove('on');
    commit();
    pal();
    cam.s = cv.clientWidth > cv.clientHeight ? cv.clientHeight / 8 : cv.clientWidth / 6;
    cam.x = cv.clientWidth / 2 - 7 * cam.s;
    cam.y = cv.clientHeight / 2 - 4.5 * cam.s;
    clamp();
    tutActive = true;
    tutStep = 0;
    tutDefCount = Object.keys(defs).length;
    updateTutUI();
}

function updateTutUI() {
    if (tutStep >= TUT_STEPS.length) {
        tutActive = false;
        $('#tutBox').hidden = true;
        localStorage.setItem('lgs_tut_done', '1');
        document.querySelectorAll('.tut-glow').forEach(el => el.classList.remove('tut-glow'));
        dirty = 1;
        return;
    }
    const tb = $('#tutBox');
    tb.hidden = false;
    tb.textContent = TUT_STEPS[tutStep].m;
    document.querySelectorAll('.tut-glow').forEach(el => el.classList.remove('tut-glow'));
    if (TUT_STEPS[tutStep].enter) TUT_STEPS[tutStep].enter();
}

// Runs every frame (from raf) and on every tap: keeps the highlight on the right element, then moves to the next step if this one is done
function checkTut(action) {
    if (!tutActive || tutStep >= TUT_STEPS.length) return;
    const stepDef = TUT_STEPS[tutStep];

    // Re-apply highlight to dynamic modal DOM targets seamlessly
    if (stepDef.hlUI) {
        const target = typeof stepDef.hlUI === 'function' ? stepDef.hlUI() : stepDef.hlUI;
        const el = target && document.querySelector(target);
        if (el && !el.classList.contains('tut-glow')) {
            document.querySelectorAll('.tut-glow').forEach(e => e.classList.remove('tut-glow'));
            el.classList.add('tut-glow');
        }
    }

    let pass = false;
    if (stepDef.advance === "tap") {
        if (action === "tap") pass = true;
    } else if (typeof stepDef.advance === "function") {
        pass = stepDef.advance();
    }

    if (pass) {
        tutStep++;
        updateTutUI();
    }
}

// Skip if running, otherwise offer to restart (clears the board)
function toggleTutorial() {
    if (tutActive) {
        tutStep = TUT_STEPS.length;
        updateTutUI();
        toast('Tutorial skipped');
    } else if (confirm("This will clear your current board to restart the tutorial. Proceed?")) {
        startTut();
    }
}

window.addEventListener('pointerup', () => checkTut("tap"));

/*
12. Menu + modals
modal(html) fills the shared dialog while #modal's click handler dispatches every button inside it
Yes
All of them
In one function
We don't talk about it
*/

const modal = h => {
    const m = $('#modal');
    m.innerHTML = `<div class="card">${h}</div>`;
    m.hidden = 0
};
const closeM = () => $('#modal').hidden = 1;
$('#bMenu').onclick = () => $('#menu').hidden = !$('#menu').hidden;
let clr = 0;
$('#menu').onclick = e => {
    const m = e.target.dataset.m;
    if (!m) return;
    if (m === 'cancelEdit') {
        cancelEditDefinition();
        $('#menu').hidden = 1;
        return
    }
    if (m == 'clr') {
        if (!clr) {
            e.target.textContent = 'Tap again to confirm';
            clr = setTimeout(() => {
                clr = 0;
                e.target.textContent = 'Clear board'
            }, 2500);
            return
        }
        clearTimeout(clr);
        clr = 0;
        e.target.textContent = 'Clear board';
        blocks = [];
        sel = null;
        commit()
    }
    if (m == 'io') modal(`<b>Import / Export</b><textarea id="ta" spellcheck="false"></textarea><div class="row"><button id="cp">Copy text</button><button id="cpl">Copy link</button><button id="im">Import</button><button id="cl">Close</button></div>`), $('#ta').value = ser();
    if (m == 'abs') modal(`<b>Abstract this board</b><small style="color:var(--mut)">Pins defined by labeled I/O cells</small><input id="nm" type="text"><label>Colour <input id="co" type="color" value="#a0cd01"></label><label><input id="ck" type="checkbox" checked> Clear board afterwards</label><div class="row"><button id="mk">Create</button><button id="cl">Cancel</button></div>`);
    if (m == 'set') settings();
    if (m == 'examples') showExamples();
    if (m == 'probe') toggleProbe();
    $('#menu').hidden = 1
};
// Copies via the Clipboard API when allowed; otherwise falls back to execCommand on the textarea,
// because some browsers still live in 2012. putInBox=true swaps the textarea's text for "text" first
function copyText(text, okMsg, putInBox) {
    const fallback = () => {
        const t = $('#ta');
        if (putInBox) t.value = text;
        t.select();
        document.execCommand('copy');
        toast(okMsg);
    };
    if (navigator.clipboard && window.isSecureContext)
        navigator.clipboard.writeText(text).then(() => toast(okMsg)).catch(fallback);
    else fallback();
}
$('#modal').onclick = e => {
    const id = e.target.id;
    if (setClick(id)) return;
    if (id === 'savePin') {
        const b = blocks.find(z => z.id === pinEdit?.id),
            q = b?.slots.find(z => z[0] === pinEdit?.at[0] && z[1] === pinEdit?.at[1] && z[2] === pinEdit?.at[2]);
        if (!q) {
            closeM();
            return
        }
        q[4] = $('#pinName').value.trim();
        q[5] = $('#pinLabel').value;
        closeM();
        pinEdit = null;
        commit();
        return
    }
    if (id === 'saveDef') {
        finishEditDefinition();
        if (!editingDefKey) closeM();
        return
    }
    if (id == 'cl' || e.target.id == 'modal') closeM();
    if (id == 'cp') {
        $('#ta').select();
        copyText($('#ta').value, 'Copied!', false);
    }
    if (id == 'cpl') {
        // Nothing reads '#b=' on page load yet, so this link currently can't be opened directly
        copyText(location.origin + location.pathname + '#b=' + $('#ta').value.trim(), 'Link copied!', true);
    }
    if (id == 'im') {
        try {
            load($('#ta').value.trim());
            closeM();
            toast('Imported')
        } catch (x) {
            toast('Invalid board string')
        }
    }
    if (id && id.startsWith('ex_')) {
        const s = EXAMPLES[id.slice(3)];
        if (s) {
            try {
                load(s);
                closeM();
                toast('Loaded: ' + EXAMPLE_NAMES[id.slice(3)])
            } catch (x) {
                toast('Could not load example')
            }
        }
    }
    if (id == 'mk') {
        const name = $('#nm').value.trim() || 'Block',
            ps = blocks.filter(b => b.t == 'io' && String(b.label || '').trim()).map(b => ({
                id: b.id,
                pin: String(b.label).trim(),
                label: String(b.label).trim(),
                k: b.slots.some(s => s[3] == 1) ? 2 : 1
            }));
        const key = 'd' + Date.now().toString(36);
        defs[key] = {
            name,
            color: $('#co').value,
            ports: ps,
            blocks: JSON.parse(JSON.stringify(blocks))
        };
        if ($('#ck').checked) {
            blocks = [];
            sel = null
        }
        commit();
        pal();
        closeM();
        toast(name + ' added to blocks')
    }
};

/*
13. Settings and reset
*/

let hr = 0;

// "hr" means hard-reset-armed, NOT hour
// I promise past-me had a reason for this garbage naming convention, but that guy is dead to me
// Renaming it now risks breaking 4 different things
function settings() {
    modal(`<b>Settings</b><label>Simulation speed: <span id="sv">${speed}</span> steps/s<input id="sp" type="range" min="1" max="127" value="${speed}" style="width:100%"></label>
<div class="row"><button id="pz">${paused?' Resume':'Pause'}</button><button id="st">Step once</button></div>
<div style="display: flex; align-items: center; justify-content: space-between; width: 100%;"><div>Expand grid: <button id="e0">↑</button><button id="e2">↓</button><button id="e3">←</button><button id="e1">→</button></div><span>(${G.x1-G.x0}×${G.y1-G.y0})</span></div>
<button id="tutBtn">${tutActive ? 'Skip tutorial' : 'Rewatch tutorial'}</button><button id="hr">Reset this app</button><button id="cl">Close</button>`)
}
$('#modal').oninput = e => {
    if (e.target.id == 'sp') {
        speed = +e.target.value;
        $('#sv').textContent = speed;
        saveSet()
    }
};

function setClick(id) {
    if (id == 'pz') {
        paused = !paused;
        settings();
        return 1
    }
    if (id == 'st') {
        step();
        dirty = 1;
        return 1
    }
    if (/^e\d$/.test(id)) {
        expand(+id[1]);
        settings();
        return 1
    }
    if (id == 'tutBtn') {
        closeM();
        toggleTutorial();
        return 1;
    }
    if (id == 'hr') {
        const b = $('#hr');
        if (!hr) {
            b.textContent = 'Are you sure? This resets ALL data!';
            hr = setTimeout(() => {
                hr = 0;
                const x = $('#hr');
                if (x) x.textContent = 'Reset this app'
            }, 8000);
            return 1
        }
        clearTimeout(hr);
        hr = 0;
        hardReset();
        return 1
    }
    return 0
}

// Wipe storage and state, then replay the tutorial as if you'd never been here
function hardReset() {
    try {
        localStorage.removeItem('lgs');
        localStorage.removeItem('lgs_s');
        localStorage.removeItem('lgs_tut_done');
    } catch (e) {}
    try {
        indexedDB.databases && indexedDB.databases().then(l => l.forEach(d => indexedDB.deleteDatabase(d.name)))
    } catch (e) {}
    blocks = [];
    defs = {};
    nodes = [];
    sel = null;
    tool = null;
    nid = 1;
    speed = 16;
    paused = 0;
    editingDefKey = null;
    editReturn = null;
    pinEdit = null;
    G = {
        x0: 0,
        y0: 0,
        x1: 12,
        y1: 12
    };
    showLab = true;
    probing = false;
    $('#bLab').classList.add('on');
    $('#bMode').textContent = 'Build';
    $('#appTitle').textContent = 'Logic Gates Sandbox';
    $('#cancelEdit').hidden = true;
    hist = [];
    histIdx = -1;
    rebuild();
    pal();
    panel();
    const W = cv.clientWidth,
        Hh = cv.clientHeight;
    cam.s = W > Hh ? Hh / 8 : W / 6;
    cam.x = W / 2 - 6 * cam.s;
    cam.y = Hh / 2 - 6 * cam.s;
    clamp();
    dirty = 1;
    pushHistory();
    closeM();
    startTut();
}

/*
14. Input: Pan/pinch/wheel
One finger drags (or taps if it barely moved), two fingers pinch-zoom, long-press a pin for settings
*/

const P = new Map();
let g = {};

// Keeps the camera from losing the board entirely
// If the board is smaller than the screen it gets centred
function clamp() {
    const W = cv.clientWidth,
        Hh = cv.clientHeight,
        s = cam.s,
        f = (v, a, b, L) => {
            const lo = L - b,
                hi = -a;
            return lo > hi ? (lo + hi) / 2 : Math.min(hi, Math.max(lo, v))
        };
    cam.x = f(cam.x, (G.x0 - 1.5) * s, (G.x1 + 1.5) * s, W);
    cam.y = f(cam.y, (G.y0 - 1.5) * s, (G.y1 + 1.5) * s, Hh)
}
let holdTimer = 0;
// Pointer down on a pin arrow starts a 460ms timer
// If the finger hasn't wandered by then, it's a long press and the Pin settings dialog opens
cv.onpointerdown = e => {
    cv.setPointerCapture(e.pointerId);
    const rect = cv.getBoundingClientRect(),
        a = arrowAt(e.clientX - rect.left, e.clientY - rect.top);
    P.set(e.pointerId, {
        x: e.clientX,
        y: e.clientY
    });
    if (P.size == 1) {
        g = {
            m: 0,
            held: false
        };
        if (a) holdTimer = setTimeout(() => {
            const p = P.get(e.pointerId);
            if (p && g.m < 8 && P.size === 1) {
                g.held = true;
                openPinSettings(a.b, a.q)
            }
        }, 460)
    } else {
        clearTimeout(holdTimer);
        g.m = 99;
        g.d = 0
    }
};
cv.onpointermove = e => {
    const p = P.get(e.pointerId);
    if (!p) return;
    if (P.size == 1) {
        const dx = e.clientX - p.x,
            dy = e.clientY - p.y;
        cam.x += dx;
        cam.y += dy;
        g.m += Math.abs(dx) + Math.abs(dy)
    }
    p.x = e.clientX;
    p.y = e.clientY;
    if (P.size == 2) {
        const [a, b] = [...P.values()], d = Math.hypot(a.x - b.x, a.y - b.y), mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
        if (g.d) {
            const ns = Math.min(200, Math.max(14, cam.s * d / g.d)),
                f = ns / cam.s;
            cam.x = mx - (mx - cam.x) * f + (mx - g.mx);
            cam.y = my - (my - cam.y) * f + (my - g.my);
            cam.s = ns
        }
        g.d = d;
        g.mx = mx;
        g.my = my
    }
    clamp();
    dirty = 1
};
cv.onpointerup = cv.onpointercancel = e => {
    if (!P.has(e.pointerId)) return;
    clearTimeout(holdTimer);
    P.delete(e.pointerId);
    if (e.type == 'pointerup' && !P.size && g.m < 8 && !g.held) {
        const r = cv.getBoundingClientRect();
        tap(e.clientX - r.left, e.clientY - r.top)
    }
};
cv.onwheel = e => {
    e.preventDefault();
    const ns = Math.min(200, Math.max(14, cam.s * (e.deltaY < 0 ? 1.1 : .9))),
        f = ns / cam.s,
        r = cv.getBoundingClientRect(),
        mx = e.clientX - r.left,
        my = e.clientY - r.top;
    cam.x = mx - (mx - cam.x) * f;
    cam.y = my - (my - cam.y) * f;
    cam.s = ns;
    clamp();
    dirty = 1
};
new ResizeObserver(() => {
    dpr = window.devicePixelRatio || 1;
    cv.width = cv.clientWidth * dpr;
    cv.height = cv.clientHeight * dpr;
    if (!inited) {
        inited = 1;
        const W = cv.clientWidth,
            Hh = cv.clientHeight;
        cam.s = W > Hh ? Hh / 8 : W / 6;
        if (!tutActive) {
            cam.x = W / 2 - (G.x0 + G.x1) / 2 * cam.s;
            cam.y = Hh / 2 - (G.y0 + G.y1) / 2 * cam.s
        }
    }
    clamp();
    dirty = 1
}).observe($('main'));

/*
15. Boot
Restore settings, then the saved board (or an empty one), then maybe the tutorial
*/

try {
    const o = JSON.parse(localStorage.getItem('lgs_s'));
    if (o && o.speed) speed = o.speed
} catch (e) {}
let saved = null;
try {
    saved = localStorage.getItem('lgs')
} catch (e) {}
try {
    if (saved) load(saved);
    else throw 0
} catch (e) {
    defs = {};
    blocks = [];
    commit()
}
pal();

// Safely initiate onboarding for completely fresh loads
if (!localStorage.getItem('lgs_tut_done') && blocks.length === 0 && Object.keys(defs).length === 0) {
    startTut();
}
