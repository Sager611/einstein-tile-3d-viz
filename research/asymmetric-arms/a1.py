import sys, itertools, time; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from gen import *
SF = [G for G in ALL48 if G[0] == (0, 1, 2)]   # 8 axis-preserving frames (sign flips, incl. mirrors)
CHAIR = [(0,0,0),(0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,0,1),(1,1,0)]
car = Carrier(CHAIR, SF, SF)
def region_k(k):
    return frozenset(tuple(2 * (k[i] * c[i] + o[i]) + 1 for i in range(3))
                     for c in CHAIR for o in itertools.product(*(range(kk) for kk in k)))
def count_dissections(k, limit=200000):
    region = region_k(k)
    place = {}
    for G in SF:
        base = car.cellset((G, (0, 0, 0)))
        for t in itertools.product(*(range(-2, 2 * max(k) + 3) for _ in range(3))):
            cs = frozenset(tuple(c[i] + 2 * t[i] for i in range(3)) for c in base)
            if cs <= region: place.setdefault(cs, []).append((G, t))
    by = {}
    for cs in place:
        for c in cs: by.setdefault(c, []).append(cs)
    n = [0]; ex = []
    def rec(unc, ch):
        if n[0] >= limit: return
        if not unc:
            n[0] += 1
            if len(ex) < 3: ex.append(list(ch))
            return
        cell = min(unc, key=lambda c: sum(1 for p in by.get(c, []) if p <= unc))
        for p in by.get(cell, []):
            if p <= unc: ch.append(p); rec(unc - p, ch); ch.pop()
    rec(region, [])
    return n[0], len(place)
for k in itertools.product((2, 3, 4), repeat=3):
    if not (k[0] <= k[1] <= k[2]): continue
    t = time.time(); n, npl = count_dissections(k)
    print(f'inflation diag{k}: {k[0]*k[1]*k[2]} copies, geometric cuttings {n}{"+" if n>=200000 else ""}  [{time.time()-t:.1f}s]', flush=True)
