import sys, itertools, time, json; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from gen import *
from a2b import carrier_cells
SF = [G for G in ALL48 if G[0] == (0, 1, 2)]
F24 = [G for G in ALL48 if det(G) == 1]
def region_of(cells, k):
    return frozenset(tuple(2 * (k[i] * cc[i] + o[i]) + 1 for i in range(3))
                     for cc in cells for o in itertools.product(*(range(kk) for kk in k)))
def all_cuttings(cells, k, frames, limit=50, tlimit=60):
    car = Carrier(cells, frames, frames)
    region = region_of(cells, k)
    place = {}
    rlo = [min(c[i] for c in region) for i in range(3)]; rhi = [max(c[i] for c in region) for i in range(3)]
    for G in frames:
        base = car.cellset((G, (0, 0, 0)))
        blo = [min(c[i] for c in base) for i in range(3)]; bhi = [max(c[i] for c in base) for i in range(3)]
        for t in itertools.product(*[range((rlo[i] - blo[i]) // 2, (rhi[i] - bhi[i]) // 2 + 1) for i in range(3)]):
            cs = frozenset(tuple(c[i] + 2 * t[i] for i in range(3)) for c in base)
            if cs <= region: place.setdefault(cs, []).append((G, t))
    by = {}
    for cs in place:
        for c in cs: by.setdefault(c, []).append(cs)
    sols = []; t0 = time.time()
    def rec(unc, ch):
        if len(sols) >= limit or time.time() - t0 > tlimit: return
        if not unc: sols.append([place[cs] for cs in ch]); return
        cell = min(unc, key=lambda c: sum(1 for p in by.get(c, []) if p <= unc))
        for p in by.get(cell, []):
            if p <= unc: ch.append(p); rec(unc - p, ch); ch.pop()
    rec(region, [])
    return sols, car
# (1) mirror contacts in the sign-flip chair cutting
chair = carrier_cells(2, 2, 2, 1, 1, 1)
sols, car = all_cuttings(chair, (2, 2, 2), SF)
print('sign-flip chair cuttings:', len(sols))
geo = sols[0]
kids = [opts[0] for opts in geo]
print('child frames (det):', [(p[0][1], det(p[0])) for p in kids])
kc = [car.cellset(k) for k in kids]
mirror_face = 0
for i in range(8):
    for j in range(i + 1, 8):
        if not car.adjacent(kc[i], kc[j]): continue
        rel = pmul(pinv(kids[i]), kids[j])
        # a reflection across the shared face plane maps tile i onto tile j exactly?
        G, t = rel
        if det(G) == -1:
            # count shared unit faces where the neighbour is the mirror image across that face
            for c in kc[i]:
                for ax in range(3):
                    for sg in (1, -1):
                        nb = list(c); nb[ax] += 2 * sg; nb = tuple(nb)
                        if nb in kc[j]:
                            plane = c[ax] + sg  # doubled coordinate of the face plane
                            refl = frozenset(tuple(2 * plane - x[m] if m == ax else x[m] for m in range(3)) for x in kc[i])
                            if refl == kc[j]: mirror_face += 1
print('shared unit faces across which the neighbour is the exact mirror image:', mirror_face)
# (2) symmetric thick/thin arm chairs with all 24 rotations, uniform inflation
for shape in [(3, 3, 3, 1, 1, 1), (3, 3, 3, 2, 2, 2), (4, 4, 4, 1, 1, 1), (4, 4, 4, 3, 3, 3)]:
    for k in (2, 3):
        cells = carrier_cells(*shape)
        if len(cells) * k ** 3 > 1400: continue
        t = time.time(); s2, _ = all_cuttings(cells, (k, k, k), F24, limit=1, tlimit=90)
        print('shape', shape, f'({len(cells)} cells) inflation {k}: cutting with 24 rotations found: {bool(s2)} [{time.time()-t:.0f}s]', flush=True)
