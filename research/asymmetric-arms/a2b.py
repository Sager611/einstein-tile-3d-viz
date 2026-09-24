import sys, itertools, time, json, multiprocessing as mp; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from gen import *
SF = [G for G in ALL48 if G[0] == (0, 1, 2)]
def carrier_cells(A, B, C, a, b, c):
    return [(x, y, z) for x in range(A) for y in range(B) for z in range(C)
            if not (x >= a and y >= b and z >= c)]
def cuttings(cells, k, limit=2000, tlimit=5):
    car = Carrier(cells, SF, SF)
    region = frozenset(tuple(2 * (k[i] * cc[i] + o[i]) + 1 for i in range(3))
                       for cc in cells for o in itertools.product(*(range(kk) for kk in k)))
    place = {}
    ext = [max(c[i] for c in cells) + 1 for i in range(3)]
    for G in SF:
        base = car.cellset((G, (0, 0, 0)))
        rlo = [min(c[i] for c in region) for i in range(3)]; rhi = [max(c[i] for c in region) for i in range(3)]
        blo = [min(c[i] for c in base) for i in range(3)]; bhi = [max(c[i] for c in base) for i in range(3)]
        rng = [range((rlo[i] - blo[i]) // 2, (rhi[i] - bhi[i]) // 2 + 1) for i in range(3)]
        for t in itertools.product(*rng):
            cs = frozenset(tuple(c[i] + 2 * t[i] for i in range(3)) for c in base)
            if cs <= region: place.setdefault(cs, []).append((G, t))
    by = {}
    for cs in place:
        for c in cs: by.setdefault(c, []).append(cs)
    n = [0]; ex = []; t0 = time.time()
    def rec(unc, ch):
        if n[0] >= limit or time.time() - t0 > tlimit: return
        if not unc:
            n[0] += 1
            if len(ex) < 2: ex.append([place[cs][0] for cs in ch])
            return
        cell = min(unc, key=lambda c: sum(1 for p in by.get(c, []) if p <= unc))
        for p in by.get(cell, []):
            if p <= unc: ch.append(p); rec(unc - p, ch); ch.pop()
    rec(region, [])
    return n[0], ex, time.time() - t0 > tlimit
def job(args):
    shape, k = args
    cells = carrier_cells(*shape)
    n, ex, to = cuttings(cells, k)
    return shape, k, n, to, [[[list(g[0]), list(g[1]), list(t)] for g, t in e] for e in ex]
if __name__ == '__main__':
    jobs = []
    for A, B, C in itertools.product((2, 3, 4), repeat=3):
        if not (A <= B <= C): continue
        for a, b, c in itertools.product(range(1, A), range(1, B), range(1, C)):
            shape = (A, B, C, a, b, c)
            # skip axis-wise stretches of a smaller shape (they inherit its cuttings)
            from math import gcd
            if any(gcd(gcd(dim, th), 99) > 1 and dim % 2 == 0 and th * 2 == dim and dim > 2
                   for dim, th in ((A, a), (B, b), (C, c))):
                continue
            for k in itertools.product((1, 2, 3, 4), repeat=3):
                if k == (1, 1, 1) or k[0] * k[1] * k[2] > 36: continue
                vol = len(carrier_cells(*shape)) * k[0] * k[1] * k[2]
                if vol > 900: continue
                jobs.append((shape, k))
    print('jobs', len(jobs), flush=True)
    jobs.sort(key=lambda j: len(carrier_cells(*j[0])) * j[1][0] * j[1][1] * j[1][2])
    res = []
    try:
        with open('./a2b.jsonl', 'w') as out, mp.Pool(mp.cpu_count()) as pool:
            for r in pool.imap_unordered(job, jobs, chunksize=2):
                res.append(r); out.write(json.dumps([r[0], r[1], r[2], r[3]]) + '\n'); out.flush()
    except OSError as err:
        sys.exit(f'cannot write ./a2b.jsonl: {err}')
    hits = [r for r in res if r[2] > 0]
    print('carrier/inflation pairs with sign-flip cuttings:', len(hits))
    for shape, k, n, to, ex in sorted(hits, key=lambda r: (r[1], r[0]))[:60]:
        print('shape A,B,C,a,b,c =', shape, ' inflation', k, ' cuttings', n, '(timeout)' if to else '')
    try:
        with open('./a2_hits.json', 'w') as fh:
            json.dump(hits, fh)
    except OSError as err:
        sys.exit(f'cannot write ./a2_hits.json: {err}')
