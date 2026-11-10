"""gen_k7te.py: writes the evaluation files of the kernel searches on 7 symbols of the 5,898 batch, cut into
small pieces.

    python gen_k7te.py CAPS [OUT] [--check] [--only=chain|prof] [--budget=N] [--stats]

CAPS: a file with a line "0: M(0) ... M(78)" (the chain caps).  The searches are those of K7/Rules.lean
(`psRules`) with the rules of PSearch.lean:

  chain    `part chainR 150`: F0 on the levels 0 .. 78 (`PS.seqBad`, `PS.seqKeepN` for the caps `W5898`)
  prof i   `part (profR i) 150`: the five profile searches FF (`PS.profBad`, `PS.profKeepN`, `PS.profKeepJ`)

Each is too large for one evaluation by the kernel, so it is cut with K7/Frontier.lean.  A cut evaluation
computes the frontier of the search below a node: the nodes where the number of rows reaches a depth and the
nodes where a profile jumps (`cutJ`), and compares it with a list written out here.  The search below the nodes
of such a list is evaluated a few nodes at a time (`allNo`); a node with a large search below it is cut again
in the same way, and a jump node with a large search below it is cut by the 5,040 words of its jumps
(`jumpsR`, `allNo_jump`), a range of words at a time, a single word with a large search through the frontier
of its walk (`jumpsR_one`).

Written below OUT (default: the directory above this script):
  K7/CapTab.lean                         the caps, the rule tables, the rules `chainR`, `profR0` .. `profR4`
  K7/CE/P*.lean, K7/CE/Top.lean          the chain search: pieces, and the cuts with the theorem `CE.top`
  K7/FE/P*.lean, K7/FE/Top{i}.lean       the profile searches: the same, theorems `FE.top0` .. `FE.top4`

Nothing here is trusted.  This script runs a copy of the search in Python to find the frontiers and the sizes
of the pieces; if a list differs from what the search in Lean computes, the kernel rejects the evaluation that
compares them, and a table that differs from its rule fails `TabAgrees`.  BUDGET bounds the calls of `go`
(weighted) of one evaluation.  --check compares the files with those in OUT instead of writing them.
"""
import itertools
import os
import sys

sys.setrecursionlimit(100000)
sys.set_int_max_str_digits(10000000)

HERE = os.path.dirname(os.path.abspath(__file__))
OPTS = {a.split('=')[0]: (a.split('=') + [''])[1] for a in sys.argv[1:] if a.startswith('--')}
ARGS = [a for a in sys.argv[1:] if not a.startswith('--')]
CHECK = '--check' in OPTS
CAPS = ARGS[0]
OUT = ARGS[1] if len(ARGS) > 1 else os.path.dirname(HERE)
K = 7
BUDGET = int(OPTS.get('--budget') or 12000)   # weighted calls of go in one evaluation
WFILE = int(OPTS.get('--wfile') or 60000)    # weighted calls of the pieces of one file
JUMPW = 1500            # extra weight of a node that tries the 5,040 jumps
FMAX = 1500             # nodes of one frontier list
CMAX = 400              # nodes of one piece
OVK = int(OPTS.get('--ovk') or 60)            # cost of a further frontier, in written nodes
TCHUNK = int(OPTS.get('--tchunk') or 150)     # declarations of the cuts in one file
FUEL = 150
HI = 78
PROFS = [[(66, 36), (66, 36)], [(50, 26), (50, 26)], [(63, 34), (34, 16)], [(66, 36), (31, 14)],
         [(31, 14), (31, 14), (34, 16), (34, 16)]]


def read_caps(fn):
    for line in open(fn):
        if line.startswith('0:'):
            return [int(t) for t in line[2:].split()]
    raise SystemExit('no caps')


W = read_caps(CAPS)
assert len(W) == HI + 1


def tables():
    perms = list(itertools.permutations(range(1, K + 1)))
    idx = {p: i for i, p in enumerate(perms)}

    def cls(p):
        i = p.index(K)
        return p[i:] + p[:i]

    cn = sorted({cls(p) for p in perms})
    cid = {c: i for i, c in enumerate(cn)}
    ci = [cid[cls(p)] for p in perms]
    exc = lambda p: p[-1:] + p[:-1]
    door = lambda x: x[2:] + (x[1], x[0])
    nx = [idx[door(exc(p))] for p in perms]
    s3 = []
    for p in perms:
        u = exc(p)
        s3.append([idx[u[3:] + q] for q in itertools.permutations(u[:3]) if cls(u[3:] + q) != cls(p)])
    return ci, nx, s3


CI, NX, S3 = tables()
NW = len(CI)


def getd(l, i, dflt=0):
    return l[i] if 0 <= i < len(l) else dflt


# ---- the rules of PSearch.lean, as in Lean ----

def seq_bad(caps, s, lo, hi):
    return lambda t, r, d: t == s and lo <= d and d <= hi and getd(caps, d) < r


def seq_keepN(caps, s, lo, hi):
    return lambda t, r, d: t <= s and any(lo <= x and d <= x and getd(caps, x) < r + getd(caps, x - d)
                                          for x in range(hi + 1))


def no_rule(t, r, d):
    return False


def prof_bad(ts):
    return lambda t, r, d: t + 1 == len(ts) and r == getd(ts, t, (0, 0))[0] and d <= getd(ts, t, (0, 0))[1]


def prof_keepN(M, ts):
    def f(t, r, d):
        T, g = getd(ts, t, (0, 0))
        return r < T and d <= g and any(T <= r + getd(M, e) for e in range(g - d + 1))
    return f


def prof_keepJ(ts):
    return lambda t, r, d: t + 1 < len(ts) and r == getd(ts, t, (0, 0))[0] and d <= getd(ts, t, (0, 0))[1]


class PSRules:
    """psRules rs A B C TB TK TJ bad keepN keepJ of K7/Rules.lean, with the cut `cutJ os ts`."""

    def __init__(self, lean, rs, A, B, C, bad, keepN, keepJ, os_, tsname, ts):
        self.lean, self.rs, self.A, self.B, self.C = lean, rs, A, B, C
        self.os, self.ts = os_, ts
        self.cut = 'cutJ [' + ', '.join(map(str, os_)) + '] ' + tsname
        self.fb, self.fn, self.fj = bad, keepN, keepJ
        self.memo = {}

    def table(self, f):
        T = 0
        for t in range(self.A):
            for r in range(self.B):
                for d in range(self.C):
                    if f(t, r, d):
                        T |= 1 << ((t * self.B + r) * self.C + d)
        return T

    def _ev(self, which, c):
        t, r, d = c
        assert t < self.A and r < self.B and d < self.C, ('outside the table', c)
        key = (which, c)
        v = self.memo.get(key)
        if v is None:
            v = (self.fb, self.fn, self.fj)[which](t, r, d)
            self.memo[key] = v
        return v

    def init(self, n, e):
        return (0, 1, n)

    def stN(self, c, n, e):
        return (c[0], c[1] + 1, c[2] + n)

    def stJ(self, c, n, e):
        return (c[0] + 1, (0 if self.rs else c[1]) + 1, (0 if self.rs else c[2]) + n)

    def bad(self, c):
        return self._ev(0, c)

    def keepN(self, c):
        return self._ev(1, c)

    def keepJ(self, c):
        return self._ev(2, c)

    def depth(self, c):
        return getd(self.os, c[0]) + c[1]

    def isjump(self, c):
        """the second part of `cutJ`: `PS.profKeepJ ts`"""
        return prof_keepJ(self.ts)(*c)

    def g_lean(self, f, c):
        """the search below the rows after a jump of the node with counters `c` and fuel `f + 1`"""
        return f'(fun U\' e n => go {self.lean} {f} U\' e ({self.lean}.stJ {self.fmt(c)} n e))'

    @staticmethod
    def fmt(c):
        return '(%d, %d, %d)' % c


class Search:
    """The search `part R fuel` of K7/Engine.lean, node by node (a node is a call of `go`), in the order of
    the search; records per node (preorder) its depth, weight, number of nodes below it, parent, whether
    it is a jump node of the cut, and for the rows after a jump the word they start at."""

    def __init__(self, R, fuel):
        self.R, self.fuel = R, fuel

    def run(self, want=None):
        R = self.R
        depth, weight, count, parent, isj, jent = [], [], [], [], [], []
        states = {}
        njump = [0]
        stack = [-1]
        cur_ent = [-1]

        def go(f, U, q, c):
            i = len(depth)
            depth.append(R.depth(c))
            weight.append(1)
            count.append(0)
            parent.append(stack[-1])
            isj.append(R.isjump(c))
            jent.append(cur_ent[-1])
            if want is not None and i in want:
                states[i] = (f, U, q, c)
            assert f > 0, 'out of fuel'
            assert not R.bad(c), 'found'
            stack.append(i)
            cur_ent.append(-1)
            if R.keepN(c):
                s = S3[q]
                for j in range(4, -1, -1):
                    walk(U, s[j], lambda U2, e, n: go(f - 1, U2, e, R.stN(c, n, e)))
            if R.keepJ(c):
                assert isj[i] and not R.keepN(c)
                weight[i] += JUMPW
                njump[0] += 1
                for k in range(NW - 1, -1, -1):
                    cur_ent[-1] = k
                    walk(U, k, lambda U2, e, n: go(f - 1, U2, e, R.stJ(c, n, e)))
                cur_ent[-1] = -1
            cur_ent.pop()
            stack.pop()
            count[i] = len(depth) - i

        def walk(U, D, g):
            n = 6
            while n > 0:
                cc = CI[D]
                if (U >> cc) & 1:
                    return
                U |= 1 << cc
                n -= 1
                g(U, D, n)
                D = NX[D]

        walk(0, 0, lambda U, e, n: go(self.fuel, U, e, R.init(n, e)))
        self.depth, self.weight, self.count, self.states = depth, weight, count, states
        self.parent, self.isj, self.jent = parent, isj, jent
        self.njump = njump[0]
        cw = [0]
        for w in weight:
            cw.append(cw[-1] + w)
        self.cw = cw
        return states


def plan(S):
    """Frontier records, in a list:
      ('front', v, Z, pieces)       the frontier below node v (None: the whole search) at depth Z
      ('jump', j, segs)             the jump node j cut by words; a seg is ('range', a, n, w) or ('one', i, k)
      ('entry', j, i, Z, pieces)    the frontier of the walk from word i of the jump node j
    a piece is ('nodes', [ids]), ('cut', k) or ('jmp', k) (k: index of a record)."""
    depth, count, cw, weight, isj = S.depth, S.count, S.cw, S.weight, S.isj
    N = len(depth)
    recs = []

    def size(i):
        return cw[i + count[i]] - cw[i]

    def scan(a, b, Z, start_top):
        """the frontier of the nodes a .. b - 1 (whole subtrees) at depth Z: (top weight, ids), stopping
        once the top weight exceeds the budget"""
        i, top, ids = a, start_top, []
        while i < b:
            if depth[i] >= Z or isj[i]:
                ids.append(i)
                i += count[i]
            else:
                top += weight[i]
                if top > 2 * BUDGET:
                    return top, ids
                i += 1
        return top, ids

    def choose(a, b, z0, start_top):
        best = None
        Z = z0 + 1
        while True:
            top, ids = scan(a, b, Z, start_top)
            if best is not None and (top + len(ids) // 2 > BUDGET or len(ids) > FMAX):
                break
            assert top <= 2 * BUDGET, 'the first frontier is too large'
            cost = len(ids) + OVK * sum(1 for i in ids if size(i) > BUDGET)
            if best is None or cost < best[0]:
                best = (cost, Z, ids)
            if all(isj[i] for i in ids):
                # no node reaches the depth: deeper cuts give the same frontier
                break
            Z += 1
        return best[1], best[2]

    def pieces_of(ids):
        pieces, cur, curw = [], [], 0
        for i in ids:
            s = size(i)
            if s > BUDGET:
                if cur:
                    pieces.append(('nodes', cur))
                    cur, curw = [], 0
                pieces.append(('jmp', solve_jump(i)) if isj[i] else ('cut', solve(i)))
            else:
                if cur and (curw + s > BUDGET or len(cur) >= CMAX):
                    pieces.append(('nodes', cur))
                    cur, curw = [], 0
                cur.append(i)
                curw += s
        if cur:
            pieces.append(('nodes', cur))
        return pieces

    def solve(v):
        if v is None:
            a, b, z0, t0 = 0, N, 0, 0
        else:
            a, b, z0, t0 = v + 1, v + count[v], depth[v], weight[v]
        Z, ids = choose(a, b, z0, t0)
        k = len(recs)
        recs.append(None)
        recs[k] = ('front', v, Z, pieces_of(ids))
        return k

    def solve_jump(j):
        a, b = j + 1, j + count[j]
        Wi = [0] * NW
        first = [None] * NW
        last = [None] * NW
        i = a
        while i < b:
            e = S.jent[i]
            assert S.parent[i] == j and e >= 0
            Wi[e] += size(i)
            if first[e] is None:
                first[e] = i
            last[e] = i + count[i]
            i += count[i]
        k = len(recs)
        recs.append(None)
        segs, sa, sw = [], 0, 0
        for e in range(NW):
            if Wi[e] > BUDGET:
                if e > sa:
                    segs.append(('range', sa, e - sa, sw))
                kk = len(recs)
                recs.append(None)
                ea, eb = first[e], last[e]
                Z, ids = choose(ea, eb, depth[ea] - 1, 0)
                recs[kk] = ('entry', j, e, Z, pieces_of(ids))
                segs.append(('one', e, kk))
                sa, sw = e + 1, 0
                continue
            if sw + Wi[e] + 1 > BUDGET:
                segs.append(('range', sa, e - sa, sw))
                sa, sw = e, 0
            sw += Wi[e] + 1
        if NW > sa:
            segs.append(('range', sa, NW - sa, sw))
        recs[k] = ('jump', j, segs)
        return k

    solve(None)
    return recs


HEAD = '/-! Generated by `tools/gen_k7te.py`: {what}. -/\n'


def node_lean(R, st):
    f, U, q, c = st
    return '(%d, %d, %d, %s)' % (f, U, q, R.fmt(c))


def want_of(recs):
    want = set()
    for r in recs:
        if r[0] == 'front':
            if r[1] is not None:
                want.add(r[1])
            ps = r[3]
        elif r[0] == 'entry':
            want.add(r[1])
            ps = r[4]
        else:
            want.add(r[1])
            ps = []
        for kind, x in ps:
            if kind == 'nodes':
                want.update(x)
    return want


def write_search(files, S, recs, prefix, dirn, R, topname):
    """Piece files `K7/{dirn}/{prefix}P{n}.lean` and the cut file `K7/{dirn}/{prefix}Top.lean`, whose
    theorem `{topname}` is `part R fuel = false`."""
    st = S.states
    pieces = []          # (weight, lean text)
    cnt = [0]
    piece_of = {}        # id(list of nodes) -> (list name, theorem name)

    def nodes_piece(ids):
        n = f'{prefix}C{cnt[0]}'
        cnt[0] += 1
        body = ',\n  '.join(node_lean(R, st[i]) for i in ids)
        w = sum(S.cw[i + S.count[i]] - S.cw[i] for i in ids)
        pieces.append((w, f'def {n}L : List (Node Cn) := [\n  {body}]\n\n'
                          f'theorem {n} : allNo {R.lean} {n}L = true := by decide +kernel\n'))
        return f'{n}L', n

    top = []             # declarations of the cut file, in order
    names = {}           # record index -> (list name of a one-node list, theorem name)

    def parts_of(ps):
        parts = []
        for kind, x in ps:
            if kind == 'nodes':
                parts.append(nodes_piece(x))
            else:
                parts.append(names[x])
        return parts

    def combine(parts):
        lst = ' ++ ('.join(p[0] for p in parts) + ')' * (len(parts) - 1)
        prf = parts[-1][1]
        for p in reversed(parts[:-1]):
            prf = f'allNo_app _ {p[1]} ({prf})'
        return lst, prf

    order = []

    def visit(k):
        r = recs[k]
        if r[0] in ('front', 'entry'):
            ps = r[3] if r[0] == 'front' else r[4]
            for kind, x in ps:
                if kind != 'nodes':
                    visit(x)
        else:
            for sg in r[2]:
                if sg[0] == 'one':
                    visit(sg[2])
        order.append(k)

    visit(0)
    for k in order:
        r = recs[k]
        name = f'{prefix}F{k}'
        if r[0] == 'front':
            _, v, Z, ps = r
            parts = parts_of(ps)
            lst, prf = combine(parts)
            L = [f'def {name}L : List (Node Cn) := {lst}', '']
            if v is None:
                L.append(f'theorem {name}cut : partL {R.lean} ({R.cut} {Z}) {S.fuel} = {name}L.map some := by')
                L.append('  decide +kernel')
                L.append('')
                L.append(f'theorem {topname} : part {R.lean} {S.fuel} = false :=')
                L.append(f'  part_of_partL _ _ _ _ {name}cut ({prf})')
            else:
                f, U, q, c = st[v]
                L.append(f'def {name}s : List (Node Cn) := [{node_lean(R, st[v])}]')
                L.append('')
                L.append(f'theorem {name}cut : goL {R.lean} ({R.cut} {Z}) {f} {U} {q} {R.fmt(c)} = '
                         f'{name}L.map some := by')
                L.append('  decide +kernel')
                L.append('')
                L.append(f'theorem {name} : allNo {R.lean} {name}s = true :=')
                L.append(f'  allNo_of_frontier _ _ _ _ {name}cut ({prf})')
                names[k] = (f'{name}s', name)
            top.append('\n'.join(L) + '\n')
        elif r[0] == 'entry':
            _, j, e, Z, ps = r
            f, U, q, c = st[j]
            parts = parts_of(ps)
            lst, prf = combine(parts)
            L = [f'def {name}L : List (Node Cn) := {lst}', '']
            L.append(f'theorem {name}cut : walkL (fun U\' e n => goL {R.lean} ({R.cut} {Z}) {f - 1} U\' e '
                     f'({R.lean}.stJ {R.fmt(c)} n e)) {U} {e} 6 = {name}L.map some := by')
            L.append('  decide +kernel')
            L.append('')
            L.append(f'theorem {name} : jumpsR {R.g_lean(f - 1, c)} {U} {e} 1 = false :=')
            L.append(f'  jumpsR_one _ _ {f - 1} {U} {e} {R.fmt(c)} _ {name}cut ({prf})')
            names[k] = None
            top.append('\n'.join(L) + '\n')
        else:
            _, j, segs = r
            f, U, q, c = st[j]
            g = R.g_lean(f - 1, c)
            prfs = []
            for sg in segs:
                if sg[0] == 'range':
                    _, a, n, w = sg
                    pn = f'{prefix}R{cnt[0]}'
                    cnt[0] += 1
                    pieces.append((w, f'theorem {pn} : jumpsR {g} {U} {a} {n} = false := by decide +kernel\n'))
                    prfs.append((pn, a, n))
                else:
                    _, e, kk = sg
                    prfs.append((f'{prefix}F{kk}', e, 1))
            prf, cum = prfs[0][0], prfs[0][2]
            assert prfs[0][1] == 0
            for pn, a, n in prfs[1:]:
                assert a == cum
                prf = f'jumpsR_app ({prf}) {pn} rfl rfl'
                cum += n
            assert cum == NW
            L = [f'def {name}s : List (Node Cn) := [{node_lean(R, st[j])}]', '']
            L.append(f'theorem {name} : allNo {R.lean} {name}s = true :=')
            L.append(f'  allNo_jump _ {f - 1} {U} {q} {R.fmt(c)} (by decide +kernel) (by decide +kernel)')
            L.append(f'    ({prf})')
            names[k] = (f'{name}s', name)
            top.append('\n'.join(L) + '\n')
    # pack the pieces into files
    pfiles, cur, curw = [], [], 0
    for w, txt in pieces:
        if cur and curw + w > WFILE:
            pfiles.append((curw, cur))
            cur, curw = [], 0
        cur.append(txt)
        curw += w
    if cur:
        pfiles.append((curw, cur))
    mods = []
    for n, (w, txts) in enumerate(pfiles):
        mod = f'K7.{dirn}.{prefix}P{n}'
        mods.append(mod)
        files[f'K7/{dirn}/{prefix}P{n}.lean'] = (
            'import K7.CapTab\n\n' + HEAD.format(what=f'{len(txts)} pieces of the search, {w} weighted calls') +
            f'\nnamespace K7.{dirn}\n\n' + '\n'.join(txts) + f'\nend K7.{dirn}\n')
    # the cuts, in order, TCHUNK declarations per file, each file importing the one before it (the memory of
    # one Lean process grows with the declarations of its file)
    groups = [top[i:i + TCHUNK] for i in range(0, len(top), TCHUNK)]
    prev = None
    for n, g in enumerate(groups):
        imps = ('import K7.CapTab\n' + ''.join(f'import {m}\n' for m in mods)) if prev is None else f'import {prev}\n'
        if prev is not None:
            imps += ''.join(f'import {m}\n' for m in mods)
        files[f'K7/{dirn}/{prefix}T{n}.lean'] = (
            imps + '\n' + HEAD.format(what=f'the cuts of the search, part {n} of {len(groups)}, {len(g)} theorems') +
            f'\nnamespace K7.{dirn}\n\n' + '\n'.join(g) + f'\nend K7.{dirn}\n')
        prev = f'K7.{dirn}.{prefix}T{n}'
    files[f'K7/{dirn}/{prefix}Top.lean'] = (
        f'import {prev}\n\n' + HEAD.format(what=f'the theorem `{topname}` of the search, in `{prev}`'))
    return f'K7.{dirn}.{prefix}Top', len(pfiles), sum(w for w, _ in pieces)


def run(R, fuel):
    S = Search(R, fuel)
    S.run()
    recs = plan(S)
    S.run(want_of(recs))
    return S, recs


def stats(tag, S, recs):
    written = 0
    nfr = nj = nent = 0
    for r in recs:
        if r[0] == 'front':
            nfr += 1
            ps = r[3]
        elif r[0] == 'entry':
            nent += 1
            ps = r[4]
        else:
            nj += 1
            ps = []
        written += sum(len(x) for kind, x in ps if kind == 'nodes')
    print(f'{tag}: {len(S.depth)} nodes, {S.njump} jump nodes, weight {S.cw[-1]}; {nfr} frontiers, {nj} jump '
          f'nodes cut by words, {nent} single words; {written} nodes written', flush=True)


def lst(l):
    return '[' + ', '.join(map(str, l)) + ']'


def main():
    files = {}
    chain = PSRules('chainR', False, 1, W[HI] + 3, HI + 6, seq_bad(W, 0, 0, HI), seq_keepN(W, 0, 0, HI),
                    no_rule, [0], '[]', [])
    profs = []
    for i, ts in enumerate(PROFS):
        A = len(ts)
        B = -(-(max(T for T, _ in ts) + 2) // 15) * 15   # a multiple of the 15 rows of a piece of TabCheck
        C = max(g for _, g in ts) + 6
        profs.append(PSRules(f'profR{i}', True, A, B, C, prof_bad(ts), prof_keepN(W, ts), prof_keepJ(ts),
                             [sum(T for T, _ in ts[:j]) for j in range(len(ts))], f'prof{i}', ts))
    T = ['import K7.Rules', 'import K7.Frontier', '',
         '/-! The caps and the rule tables of the kernel searches of the 5,898 batch (generated by',
         '`tools/gen_k7te.py`; see there).  Nothing here is trusted: `TabAgrees` checks each table against its rule. -/',
         '', 'namespace K7', '', 'open SuperpermLowerBounds', '',
         '/-- Equality of nodes is decidable (given directly: the search for the instance of a tuple of six',
         'numbers gives up). -/',
         'instance decNode : DecidableEq (Node Cn) := instDecidableEqProd', '',
         'instance decONode : DecidableEq (Option (Node Cn)) := Option.instDecidableEq', '',
         '/-- Upper bounds for the rows of a chain on 7 symbols with 0 to 78 holes. -/',
         f'def W5898 : List Nat := {lst(W)}', '']
    T.append(f'/-- `PS.seqBad [W5898] 0 0 78 t r d` as bit `(t * {chain.B} + r) * {chain.C} + d`. -/')
    T.append(f'def TBc : Nat := {chain.table(chain.fb)}')
    T.append(f'/-- `PS.seqKeepN [W5898] 0 0 78 t r d` as bit `(t * {chain.B} + r) * {chain.C} + d`. -/')
    T.append(f'def TKc : Nat := {chain.table(chain.fn)}')
    T.append('')
    T.append('/-- The rules of the chain search F0 (levels 0 to 78). -/')
    T.append(f'def chainR : Rules Cn := psRules false {chain.A} {chain.B} {chain.C} TBc TKc 0 '
             f'(PS.seqBad [W5898] 0 0 {HI}) (PS.seqKeepN [W5898] 0 0 {HI}) PS.noRule')
    T.append('')
    for i, (R, ts) in enumerate(zip(profs, PROFS)):
        tl = '[' + ', '.join('(%d, %d)' % p for p in ts) + ']'
        T.append(f'/-- The profile {tl}. -/')
        T.append(f'def prof{i} : List (Nat × Nat) := {tl}')
        T.append(f'def TBp{i} : Nat := {R.table(R.fb)}')
        T.append(f'def TKp{i} : Nat := {R.table(R.fn)}')
        T.append(f'def TJp{i} : Nat := {R.table(R.fj)}')
        T.append(f'/-- The rules of the profile search of `prof{i}`. -/')
        T.append(f'def profR{i} : Rules Cn := psRules true {R.A} {R.B} {R.C} TBp{i} TKp{i} TJp{i} '
                 f'(PS.profBad prof{i}) (PS.profKeepN W5898 prof{i}) (PS.profKeepJ prof{i})')
        T.append('')
    T += ['end K7', '']
    files['K7/CapTab.lean'] = '\n'.join(T)
    # the checks of the tables, in pieces of RW rows; the heavy rule seqKeepN of the chains one piece per file
    RW = 15
    tabs = [('Bc', chain, 'TBc', f'PS.seqBad [W5898] 0 0 {HI}', False),
            ('Kc', chain, 'TKc', f'PS.seqKeepN [W5898] 0 0 {HI}', True),
            ('Jc', chain, '0', 'PS.noRule', False)]
    for i, R in enumerate(profs):
        tabs += [(f'B{i}', R, f'TBp{i}', f'PS.profBad prof{i}', False),
                 (f'K{i}', R, f'TKp{i}', f'PS.profKeepN W5898 prof{i}', False),
                 (f'J{i}', R, f'TJp{i}', f'PS.profKeepJ prof{i}', False)]
    head = ['import K7.Prove', 'import K7.CapTab', '',
            '/-! Generated by `tools/gen_k7te.py`: pieces of the checks of the rule tables (`K7/TabCheck.lean`). -/',
            '', 'namespace K7', '', 'open SuperpermLowerBounds', '']
    tfiles = {}
    comb = []
    for nm, R, tb, fn, single in tabs:
        m = -(-R.B // RW)
        names = []
        for t in range(R.A):
            for k in range(m):
                th = f'tab{nm}_{t}_{k}'
                fnm = f'{nm}{len(names)}' if single else ('Chain' if nm.endswith('c') else 'Prof')
                names.append(th)
                tfiles.setdefault(fnm, []).append(
                    'set_option maxRecDepth 100000 in\n'
                    f'theorem {th} : RowsAgree {R.B} {R.C} {tb} ({fn}) {t} ({k} * {RW}) {RW} = true := by\n'
                    '  decide +kernel\n')
        comb.append(f'theorem tab{nm} : TabAgrees {R.A} {R.B} {R.C} {tb} ({fn}) = true :=\n'
                    f'  tabAgrees_of_rows (w := {RW}) (m := {m}) (by norm_num) (by\n'
                    '    intro t ht k hk\n'
                    '    interval_cases t <;> interval_cases k\n'
                    '    exacts [' + ', '.join(names) + '])\n')
    for fnm, ths in tfiles.items():
        files[f'K7/TabCheck/{fnm}.lean'] = '\n'.join(head) + '\n' + '\n'.join(ths) + '\nend K7\n'
    files['K7/TabCheck.lean'] = (
        ''.join(f'import K7.TabCheck.{fnm}\n' for fnm in tfiles) + 'import Mathlib.Tactic.IntervalCases\n\n'
        '/-! The rule tables of `K7/CapTab.lean` agree with the rules of `PSearch.lean` (generated by\n'
        '`tools/gen_k7te.py`; the pieces, checked by the kernel, are in `K7/TabCheck/`). -/\n\n'
        'namespace K7\n\nopen SuperpermLowerBounds\n\n' + '\n'.join(comb) + '\nend K7\n')
    only = OPTS.get('--only')
    if only in (None, 'chain'):
        S, recs = run(chain, FUEL)
        stats('chain', S, recs)
        root, nf, wsum = write_search(files, S, recs, 'E', 'CE', chain, 'top')
        print(f'  {nf} piece files, pieces {wsum} weighted calls', flush=True)
    if only in (None, 'prof'):
        for i, R in enumerate(profs):
            S, recs = run(R, FUEL)
            stats(f'profile {i}', S, recs)
            root, nf, wsum = write_search(files, S, recs, f'P{i}', 'FE', R, f'top{i}')
            print(f'  {nf} piece files, pieces {wsum} weighted calls', flush=True)
    tot = sum(len(t) for t in files.values())
    print(f'{len(files)} files, {tot / 1e6:.1f} MB')
    if '--stats' in OPTS:
        return
    bad = 0
    for path, txt in sorted(files.items()):
        p = os.path.join(OUT, path)
        if CHECK:
            if not os.path.isfile(p) or open(p, encoding='utf-8').read() != txt:
                print('differs:', path)
                bad += 1
        else:
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, 'w', encoding='utf-8', newline='\n') as f:
                f.write(txt)
    if CHECK:
        print(len(files), 'files,', bad, 'differ')
        sys.exit(1 if bad else 0)
    print(len(files), 'files written')


if __name__ == '__main__':
    main()
