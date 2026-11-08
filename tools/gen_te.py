"""gen_te.py: writes the evaluation files of the two kernel searches on 6 symbols, cut into small pieces.

    python3 gen_te.py [OUT] [--check]

The searches are those of K6/CapRules.lean (the chain caps, `part (capRules [W6] 0 20 TB_0_20 TK_0_20) 130`)
and of K6/TightRules.lean (the tight case, `part (famRules T 2 1 0 1 0) 40` for T = 1, 2, 3 trails).  Each is
too large for one evaluation by the kernel within the memory of the Almanac's judge, so it is cut with
K6/Frontier.lean: a cut evaluation computes the frontier of the search at a depth (the list of nodes where the
number of rows reaches the depth) and compares it with a list written out here; the search below the nodes
of that list is evaluated a few nodes at a time (`allNo`), and a node with a large search below it is cut
again in the same way.

Written below OUT (default: the directory above this script):
  K6/CE/*.lean, K6/CapEval.lean       the chain search: pieces and the theorem `capEval`
  K6/TE/*.lean, K6/TightAll.lean      the tight case: pieces and the theorems `tightAll1` to `tightAll3`

Nothing here is trusted.  This script runs a copy of the search in Python to find the frontiers and the sizes
of the pieces; if a list differs from what the search in Lean computes, the kernel rejects the evaluation that
compares them.  BUDGET bounds the calls of `go` (weighted) of one evaluation.  --check compares the files
with those in OUT instead of writing them.
"""
import itertools
import os
import sys

sys.setrecursionlimit(20000)
sys.set_int_max_str_digits(1000000)

HERE = os.path.dirname(os.path.abspath(__file__))
ARGS = [a for a in sys.argv[1:] if not a.startswith('--')]
CHECK = '--check' in sys.argv
OUT = ARGS[0] if ARGS else os.path.dirname(HERE)
K = 6
BUDGET = 12000          # weighted calls of go in one evaluation
LEAFW = 3000            # weight of a node where the leaf test deadB runs
FMAX = 1500             # nodes of one frontier list
CMAX = 400              # nodes of one piece
W = [4, 4, 7, 7, 10, 10, 11, 13, 14, 15, 16, 17, 19, 19, 22, 23, 24, 25, 26, 27, 28]
FUEL_T = 40
FUEL_C = 130


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
LOOPM = [(1 << CI[i]) | (1 << CI[NX[i]]) | (1 << CI[NX[NX[i]]]) | (1 << CI[NX[NX[NX[i]]]]) for i in range(720)]


def deadB(U):
    for c in range(120):
        if not (U >> c) & 1:
            if all(not ((LOOPM[i] >> c) & 1) or (LOOPM[i] & U) != 0 for i in range(720)):
                return True
    return False


class TightRules:
    """famRules T 2 1 0 1 0 of K6/TightRules.lean (n0 = n1 = 1: one part, the gate always holds)."""

    def __init__(self, T):
        self.T = T
        eW = [W[h] - h for h in range(21)]
        best = [[0] * 21]
        for n in range(1, 4):
            best.append([max(eW[x] + best[n - 1][g - x] for x in range(g + 1)) for g in range(21)])
        self.bt = best
        self.need = 8 + 4 * (T - 1)
        self.G = 20 - 5 * (T - 1)
        self.g0 = 2
        self.lean = f'famRules {T} 2 1 0 1 0'

    def init(self, n, e):
        return (0, 1, n, 0, 0, 0, 0, 1, e if self.g0 == 1 else 0, 0)

    def stN(self, c, n, e):
        t, r, d, A, B, r1, d1, z, k0, k1 = c
        return (t, r + 1, d + n, A, B, r1, d1, z + 1, e if z + 1 == self.g0 else k0, k1)

    def stJ(self, c, n, e):
        t, r, d, A, B, r1, d1, z, k0, k1 = c
        return (t + 1, 1, n, A + r, B + d, r if t == 0 else r1, d if t == 0 else d1, z + 1,
                e if z + 1 == self.g0 else k0, e if t == 0 else k1)

    def _ord(self, c):
        t, r, d, A, B, r1, d1 = c[:7]
        return t == 0 or r + d1 <= r1 + d

    def keepN(self, c):
        t, r, d, A, B = c[:5]
        return B + d <= self.G and self.need + d + B <= r + A + self.bt[self.T - t][self.G - B - d]

    def keepJ(self, c):
        t, r, d, A, B = c[:5]
        return (t + 1 < self.T and self._ord(c) and B + d <= self.G and
                self.need + d + B <= r + A + self.bt[self.T - t - 1][self.G - B - d])

    def leaf(self, c):
        """the conditions of `bad` before deadB"""
        t, r, d, A, B = c[:5]
        return t + 1 == self.T and self._ord(c) and B + d <= self.G and self.need + d + B <= r + A

    @staticmethod
    def depth(c):
        return c[7]

    @staticmethod
    def fmt(c):
        return '⟨' + ', '.join(map(str, c)) + '⟩'


class CapRules:
    """capRules [W6] 0 20 TB_0_20 TK_0_20 of K6/CapRules.lean: counters (rows, holes)."""
    lean = 'capRules [W6] 0 20 TB_0_20 TK_0_20'

    def init(self, n, e):
        return (1, n)

    def stN(self, c, n, e):
        return (c[0] + 1, c[1] + n)

    def stJ(self, c, n, e):
        return c

    @staticmethod
    def cap(x):
        return W[x] if x < len(W) else 0

    def keepN(self, c):
        r, d = c
        assert r < 64 and d < 32
        return any(d <= x and self.cap(x) < r + self.cap(x - d) for x in range(21))

    def keepJ(self, c):
        return False

    def bad(self, c):
        r, d = c
        assert r < 64 and d < 32
        return 0 <= d <= 20 and self.cap(d) < r

    def leaf(self, c):
        return False

    @staticmethod
    def depth(c):
        return c[0]

    @staticmethod
    def fmt(c):
        return '(%d, %d)' % c


class Search:
    """The search `part R fuel` of K6/Engine.lean, node by node (a node is a call of `go`), in the order of
    the search; records per node (preorder) its depth, its weight and the number of nodes below it."""

    def __init__(self, R, fuel):
        self.R, self.fuel = R, fuel

    def run(self, want=None):
        R = self.R
        depth, weight, count = [], [], []
        states = {}

        def go(f, U, q, c):
            i = len(depth)
            depth.append(R.depth(c))
            weight.append(1)
            count.append(0)
            if want is not None and i in want:
                states[i] = (f, U, q, c)
            assert f > 0, 'out of fuel'
            if isinstance(R, CapRules):
                assert not R.bad(c), 'found'
            elif R.leaf(c):
                weight[i] += LEAFW
                assert deadB(U), 'found'
            if R.keepN(c):
                for j in range(4, -1, -1):
                    walk(U, S3[q][j], lambda U2, e, n: go(f - 1, U2, e, R.stN(c, n, e)))
            if R.keepJ(c):
                for k in range(719, -1, -1):
                    walk(U, k, lambda U2, e, n: go(f - 1, U2, e, R.stJ(c, n, e)))
            count[i] = len(depth) - i

        def walk(U, D, g):
            n = 5
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
        # cumulative weights for range sums
        cw = [0]
        for w in weight:
            cw.append(cw[-1] + w)
        self.cw = cw
        return states


def plan(S):
    """The cuts: a list of frontiers; frontier k = (node or None for the root, depth Z, list of pieces);
    a piece is ('nodes', [ids]) or ('cut', frontier index)."""
    depth, count, cw = S.depth, S.count, S.cw
    N = len(depth)
    fronts = []

    def sub(v):
        return (0, N, 0) if v is None else (v + 1, v + count[v], depth[v])

    def frontier(v, Z):
        a, b, _ = sub(v)
        top = (0 if v is None else 1) + sum(S.weight[i] for i in range(a, b) if depth[i] < Z)
        ids = [i for i in range(a, b) if depth[i] == Z]
        return top, ids

    def size(i):
        return cw[i + count[i]] - cw[i]

    def solve(v):
        a, b, z0 = sub(v)
        maxd = max(depth[a:b])
        best = None
        for Z in range(z0 + 1, maxd + 1):
            top, ids = frontier(v, Z)
            if best is not None and (top + len(ids) // 2 > BUDGET or len(ids) > FMAX):
                break
            best = (Z, ids)
        Z, ids = best
        k = len(fronts)
        fronts.append(None)
        pieces, cur, curw = [], [], 0
        for i in ids:
            s = size(i)
            if s > BUDGET:
                if cur:
                    pieces.append(('nodes', cur))
                    cur, curw = [], 0
                pieces.append(('cut', solve(i)))
            else:
                if cur and (curw + s > BUDGET or len(cur) >= CMAX):
                    pieces.append(('nodes', cur))
                    cur, curw = [], 0
                cur.append(i)
                curw += s
        if cur:
            pieces.append(('nodes', cur))
        fronts[k] = (v, Z, pieces)
        return k

    solve(None)
    return fronts


HEAD = '/-! Generated by `tools/gen_te.py`: {what}. -/\n'


def node_lean(R, st):
    f, U, q, c = st
    return '(%d, %d, %d, %s)' % (f, U, q, R.fmt(c))


def write_search(files, S, fronts, prefix, dirn, imports, R, cutname, cnt):
    """Lean files of one search; returns (file of the root frontier, its theorem, its list name)."""
    states = S.states
    names = {}
    chunk_no = [0]

    def piece_files(k):
        v, Z, pieces = fronts[k]
        parts = []     # (list name, theorem name, module)
        for kind, x in pieces:
            if kind == 'nodes':
                j = chunk_no[0]
                chunk_no[0] += 1
                name = f'{prefix}C{j}'
                mod = f'K6.{dirn}.{name}'
                body = ',\n  '.join(node_lean(R, states[i]) for i in x)
                w = sum(S.cw[i + S.count[i]] - S.cw[i] for i in x)
                txt = (f'import {imports}\n\n' + HEAD.format(what=f'{len(x)} nodes of the search, {w} weighted calls') +
                       f'\nnamespace K6.{dirn}\n\n'
                       f'def {name}L : List (Node {cnt}) := [\n  {body}]\n\n'
                       f'theorem {name} : allNo ({R.lean}) {name}L = true := by decide +kernel\n\n'
                       f'end K6.{dirn}\n')
                files[f'K6/{dirn}/{name}.lean'] = txt
                parts.append((f'{name}L', name, mod))
            else:
                parts.append(names[x])
        return parts

    order = []

    def visit(k):
        for kind, x in fronts[k][2]:
            if kind == 'cut':
                visit(x)
        order.append(k)

    visit(0)
    for k in order:
        v, Z, pieces = fronts[k]
        parts = piece_files(k)
        name = f'{prefix}F{k}'
        mod = f'K6.{dirn}.{name}'
        mods = sorted({m for _, _, m in parts})
        lst = ' ++ ('.join(p[0] for p in parts) + ')' * (len(parts) - 1)
        prf = parts[-1][1]
        for p in reversed(parts[:-1]):
            prf = f'allNo_app _ {p[1]} ({prf})'
        L = [f'import {m}' for m in mods] + ['']
        L.append(HEAD.format(what=f'the frontier of the search {"of the whole search" if v is None else "below a node"} '
                                  f'at depth {Z}, {len(parts)} pieces').rstrip('\n'))
        L += ['', f'namespace K6.{dirn}', '']
        L.append(f'def {name}L : List (Node {cnt}) := {lst}')
        L.append('')
        if v is None:
            L.append(f'theorem {name}cut : partL ({R.lean}) ({cutname} {Z}) {S.fuel} = {name}L.map some := by')
            L.append('  decide +kernel')
            L.append('')
            L.append(f'theorem {name} : part ({R.lean}) {S.fuel} = false :=')
            L.append(f'  part_of_partL _ _ _ _ {name}cut ({prf})')
        else:
            st = states[v]
            f, U, q, c = st
            L.append(f'def {name}s : List (Node {cnt}) := [{node_lean(R, st)}]')
            L.append('')
            L.append(f'theorem {name}cut : goL ({R.lean}) ({cutname} {Z}) {f} {U} {q} {R.fmt(c)} = '
                     f'{name}L.map some := by')
            L.append('  decide +kernel')
            L.append('')
            L.append(f'theorem {name} : allNo ({R.lean}) {name}s = true :=')
            L.append(f'  allNo_of_frontier _ _ _ _ {name}cut ({prf})')
        L += ['', f'end K6.{dirn}', '']
        files[f'K6/{dirn}/{name}.lean'] = '\n'.join(L)
        if v is not None:
            names[k] = (f'{name}s', name, mod)
    return f'K6.{dirn}.{prefix}F0', f'K6.{dirn}.{prefix}F0'


def run(R, fuel):
    S = Search(R, fuel)
    S.run()
    fronts = plan(S)
    want = set()
    for v, Z, pieces in fronts:
        if v is not None:
            want.add(v)
        for kind, x in pieces:
            if kind == 'nodes':
                want.update(x)
    S.run(want)
    return S, fronts


def stats(tag, S, fronts):
    nchunks = sum(1 for _, _, p in fronts for kind, _ in p if kind == 'nodes')
    tops = []
    for v, Z, p in fronts:
        a, b = (0, len(S.depth)) if v is None else (v + 1, v + S.count[v])
        tops.append(sum(S.weight[i] for i in range(a, b) if S.depth[i] < Z))
    chunks = [sum(S.cw[i + S.count[i]] - S.cw[i] for i in x) for _, _, p in fronts for kind, x in p
              if kind == 'nodes']
    print(f'{tag}: {len(S.depth)} nodes, weight {S.cw[-1]}, {len(fronts)} frontiers (largest cut evaluation '
          f'{max(tops)}), {nchunks} pieces (largest {max(chunks)}, sum {sum(chunks)})')


def main():
    files = {}
    # the chain search
    R = CapRules()
    S, fronts = run(R, FUEL_C)
    stats('chain caps', S, fronts)
    write_search(files, S, fronts, 'E', 'CE', 'K6.CapCut', R, 'cutR', '(Nat × Nat)')
    files['K6/CapEval.lean'] = '\n'.join([
        'import K6.CE.EF0', '',
        '/-!', '# Evaluation by the kernel: the chain search on 6 symbols with the caps `W6` (0 to 20 holes)', '',
        'One search, 52,386 calls of `go`, cut into pieces by `tools/gen_te.py` (see `K6/Frontier.lean`); the',
        'files of the pieces are in `K6/CE/`.  No Mathlib is loaded.', '-/', '',
        'namespace K6', '',
        'theorem capEval : part (capRules [W6] 0 20 TB_0_20 TK_0_20) 130 = false := CE.EF0', '',
        'end K6', '', '#print axioms K6.capEval', ''])
    # the tight case
    roots = []
    for T in (1, 2, 3):
        R = TightRules(T)
        S, fronts = run(R, FUEL_T)
        stats(f'tight case, {T} trails', S, fronts)
        write_search(files, S, fronts, f'T{T}', 'TE', 'K6.TightCut', R, 'cutZ', 'FC')
        roots.append(f'K6.TE.T{T}F0')
    L = [f'import {m}' for m in roots] + [
        '', '/-!', '# All parts of the search of the tight case', '',
        '`tightAll T`: for `T = 1, 2, 3` trails, the search answers `false` (one part each, `n0 = n1 = 1`).',
        'Each search is cut into pieces by `tools/gen_te.py` (see `K6/Frontier.lean`); the files of the',
        'pieces are in `K6/TE/`.', '-/', '', 'namespace K6', '']
    for T in (1, 2, 3):
        L += [f'theorem tightAll{T} : ∀ p0, p0 < 1 → ∀ p1, p1 < 1 →',
              f'    part (famRules {T} 2 1 p0 1 p1) 40 = false := by',
              '  intro p0 h0 p1 h1',
              '  obtain rfl : p0 = 0 := by omega',
              '  obtain rfl : p1 = 0 := by omega',
              f'  exact TE.T{T}F0', '']
    L += ['end K6', '']
    files['K6/TightAll.lean'] = '\n'.join(L)
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
