"""Generic carrier pipeline: rep-8 polycube carrier + 8-slot panel features -> closure -> profile -> atlas -> halving.
Coordinates: integer units of 1/8 cell (so feature offsets 1/8, 1/4 are integers). Cells keyed by integer min corner.
"""
import itertools, functools

PERMS = list(itertools.permutations(range(3)))

def det(G):
    p, s = G
    inv = sum(1 for i in range(3) for j in range(i + 1, 3) if p[i] > p[j])
    return (-1) ** inv * s[0] * s[1] * s[2]

ALL48 = [(p, s) for p in PERMS for s in itertools.product((1, -1), repeat=3)]

def app(G, x):
    p, s = G
    return tuple(s[i] * x[p[i]] for i in range(3))

def compose(G, H):
    p, s = G; q, r = H
    return (tuple(q[p[i]] for i in range(3)), tuple(s[i] * r[p[i]] for i in range(3)))

def inv(G):
    p, s = G; q = [0] * 3; r = [0] * 3
    for i in range(3):
        q[p[i]] = i; r[p[i]] = s[i]
    return (tuple(q), tuple(r))

def pmul(A, B):
    return (compose(A[0], B[0]), tuple(a + b for a, b in zip(app(A[0], B[1]), A[1])))

def pinv(A):
    Gi = inv(A[0])
    return (Gi, tuple(-x for x in app(Gi, A[1])))

ID = ((0, 1, 2), (1, 1, 1))
IDP = (ID, (0, 0, 0))
OFFS = [(1, 2), (1, -2), (-1, 2), (-1, -2), (2, 1), (2, -1), (-2, 1), (-2, -1)]  # eighths of a cell


class Carrier:
    def __init__(self, cells, frames_proper, frames_all):
        self.cells = [tuple(c) for c in cells]
        self.FP = frames_proper
        self.FA = frames_all
        cs = set(self.cells)
        # panels: (centre*8 as ints doubled to stay integral -> use 16ths), normal
        self.slots = []  # (position in 1/16 units, panel index)
        self.panels = []
        for c in self.cells:
            for ax in range(3):
                for sg in (1, -1):
                    n = [0, 0, 0]; n[ax] = sg
                    if tuple(c[i] + n[i] for i in range(3)) in cs:
                        continue
                    centre = [16 * c[i] + 8 for i in range(3)]
                    centre[ax] += 8 * sg
                    a, b = [i for i in range(3) if i != ax]
                    pid = len(self.panels)
                    self.panels.append((tuple(centre), tuple(n)))
                    for u, v in OFFS:
                        p = list(centre); p[a] += 2 * u; p[b] += 2 * v
                        self.slots.append((tuple(p), pid))
        self.S = len(self.slots)

    @functools.lru_cache(maxsize=None)
    def cellset(self, pose):
        G, t = pose
        out = []
        for c in self.cells:
            ctr = app(G, tuple(2 * x + 1 for x in c))
            out.append(tuple(ctr[i] + 2 * t[i] for i in range(3)))
        return frozenset(out)  # doubled cell centres

    @functools.lru_cache(maxsize=None)
    def shell(self, A):
        out = set()
        for c in A:
            for ax in range(3):
                for sg in (1, -1):
                    nb = list(c); nb[ax] += 2 * sg; nb = tuple(nb)
                    if nb not in A:
                        out.add(nb)
        return frozenset(out)

    def adjacent(self, A, B):
        return not self.shell(A).isdisjoint(B)

    def slotpos(self, pose, k):
        G, t = pose
        p = app(G, self.slots[k][0])
        return tuple(p[i] + 16 * t[i] for i in range(3))

    def candidates(self):
        root = self.cellset(IDP)
        sh = self.shell(root)
        out = set()
        for G in self.FA:
            for c in self.cells:
                img = app(G, tuple(2 * x + 1 for x in c))
                for s in sh:
                    t2 = tuple(a - b for a, b in zip(s, img))
                    if any(x % 2 for x in t2):
                        continue
                    pose = (G, tuple(x // 2 for x in t2))
                    if not (self.cellset(pose) & root):
                        out.add(pose)
        return sorted(out)

    def setup(self):
        self.CAND = self.candidates()
        self.CIDX = {p: i for i, p in enumerate(self.CAND)}
        rootpos = {self.slotpos(IDP, k): k for k in range(self.S)}
        self.PAIRS = []
        for p in self.CAND:
            pr = []
            for m in range(self.S):
                w = self.slotpos(p, m)
                if w in rootpos:
                    pr.append((rootpos[w], m))
            self.PAIRS.append(pr)
        return self

    def closure(self, kids):
        kc = [self.cellset(h) for h in kids]
        base = set()
        for i, A in enumerate(kids):
            for j, B in enumerate(kids):
                if i != j and self.adjacent(kc[i], kc[j]):
                    base.add(pmul(pinv(A), B))
        C = set(base); fr = set(base)
        while fr:
            new = set()
            for r in fr:
                R2 = (r[0], tuple(2 * x for x in r[1]))
                for i, A in enumerate(kids):
                    for H in kids:
                        Bj = pmul(R2, H)
                        if self.adjacent(kc[i], self.cellset(Bj)):
                            rel = pmul(pinv(A), Bj)
                            if rel not in C:
                                new.add(rel)
            C |= new; fr = new
        return C

    def profile(self, contacts):
        par = list(range(self.S)); odd = [0] * self.S
        def find(x):
            if par[x] == x:
                return x, 0
            r, o = find(par[x]); par[x] = r; odd[x] ^= o
            return r, odd[x]
        for r in contacts:
            if r not in self.CIDX:
                return None, 'contact-not-candidate'
            for a, b in self.PAIRS[self.CIDX[r]]:
                (ra, oa), (rb, ob) = find(a), find(b)
                if ra == rb:
                    if oa ^ ob != 1:
                        return None, 'parity-conflict'
                else:
                    par[ra] = rb; odd[ra] = oa ^ ob ^ 1
        roots = {}; prof = []
        for x in range(self.S):
            r, o = find(x)
            roots.setdefault(r, len(roots) + 1)
            prof.append(roots[r] * (-1 if o else 1))
        return prof, len(roots)

    def atlas(self, prof):
        return {self.CAND[i] for i, pr in enumerate(self.PAIRS)
                if pr and all(prof[a] == -prof[b] for a, b in pr)}

    def halving(self, atlas, kids, k=2):
        body = frozenset().union(*(self.cellset(c) for c in kids))
        kc = [self.cellset(c) for c in kids]
        seen = set(); halved = set()
        for Ci in kids:
            for c in atlas:
                N = pmul(Ci, c)
                for Hj in kids:
                    GB = compose(N[0], inv(Hj[0]))
                    kt = tuple(a - b for a, b in zip(N[1], app(GB, Hj[1])))
                    pc = (GB, kt)
                    if pc in seen:
                        continue
                    seen.add(pc)
                    Bk = [self.cellset(pmul(pc, h)) for h in kids]
                    if body & frozenset().union(*Bk):
                        continue
                    ok = True; touch = False
                    for i, C2 in enumerate(kids):
                        for j, H2 in enumerate(kids):
                            if self.adjacent(kc[i], Bk[j]):
                                touch = True
                                if pmul(pinv(C2), pmul(pc, H2)) not in atlas:
                                    ok = False; break
                        if not ok:
                            break
                    if not (ok and touch):
                        continue
                    if any(x % k for x in kt):
                        return False, 'odd-parent-translation'
                    h = (GB, tuple(x // k for x in kt))
                    if h not in atlas:
                        return False, 'parent-outside-atlas'
                    halved.add(h)
        return halved == atlas, ('equal' if halved == atlas else f'strict-subset {len(halved)}/{len(atlas)}')

    def evaluate(self, kids):
        C = self.closure(kids)
        prof, m = self.profile(C)
        if prof is None:
            return {'fail': m}
        A = self.atlas(prof)
        proper = all(det(p[0]) == 1 for p in A)
        eq, why = self.halving(A, kids)
        return {'closure': len(C), 'classes': m, 'atlas': len(A), 'proper': proper, 'halving': eq, 'why': why, 'prof': prof, 'A': A}


def dissections(carrier, k, frames):
    """All exact covers of the k-scaled carrier by carrier copies in the given frames (cells = doubled centres)."""
    region = frozenset(tuple(2 * (k * a + o) + 1 for a, o in zip(c, off))
                       for c in carrier.cells for off in itertools.product(range(k), repeat=3))
    pl = []
    for G in frames:
        base = carrier.cellset((G, (0, 0, 0)))
        lo = [min(c[i] for c in region) - max(abs(x) for c in base for x in c) - 2 for i in range(3)]
        hi = [max(c[i] for c in region) + max(abs(x) for c in base for x in c) + 2 for i in range(3)]
        for t in itertools.product(*(range(lo[i] // 2, hi[i] // 2 + 1) for i in range(3))):
            cs = frozenset(tuple(c[i] + 2 * t[i] for i in range(3)) for c in base)
            if cs <= region:
                pl.append(((G, t), cs))
    by = {}
    for p in pl:
        for c in p[1]:
            by.setdefault(c, []).append(p)
    sols = []
    def rec(unc, ch):
        if not unc:
            sols.append(tuple(sorted(ch))); return
        cell = min(unc, key=lambda c: sum(1 for p in by.get(c, []) if p[1] <= unc))
        for p in by.get(cell, []):
            if p[1] <= unc:
                ch.append(p[0]); rec(unc - p[1], ch); ch.pop()
    rec(region, [])
    return sorted(set(sols))
