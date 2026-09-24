import sys; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from gen import *
from a2b import carrier_cells
from a3 import all_cuttings
SF = [G for G in ALL48 if G[0] == (0, 1, 2)]
chair = carrier_cells(2, 2, 2, 1, 1, 1)
sols, car = all_cuttings(chair, (2, 2, 2), SF)
kids = [o[0] for o in sols[0]]
C = car.closure(kids)
print('contact closure size:', len(C))
root = car.cellset(IDP)
panels = car.panels  # (centre in 1/16 units, outward normal)
flat = set()
for rel in C:
    B = car.cellset(rel)
    if det(rel[0]) != -1: continue
    for pid, (ctr, n) in enumerate(panels):
        ax = next(i for i in range(3) if n[i]); 
        # the unit cell of the root behind this panel, and the cell in front
        cell_in = tuple((ctr[i] - (8 * n[i] if i == ax else 0)) // 8 for i in range(3))
        front = tuple(cell_in[i] + 2 * n[i] if False else cell_in[i] for i in range(3))
        c2 = tuple(ctr[i] // 8 - n[i] if i == ax else ctr[i] // 8 for i in range(3))
        cin = tuple(ctr[i] // 8 + (-1 if (i == ax and n[i] > 0) else 0) if i == ax else ctr[i] // 8 for i in range(3))
        # doubled centre of inner cell and outer cell
        inner = tuple((2 * (ctr[i] // 16) + 1) if i != ax else (ctr[i] // 8 - n[i]) for i in range(3))
        outer = tuple((2 * (ctr[i] // 16) + 1) if i != ax else (ctr[i] // 8 + n[i]) for i in range(3))
        if inner in root and outer in B:
            plane = ctr[ax] // 8
            refl = frozenset(tuple(2 * plane - x[m] if m == ax else x[m] for m in range(3)) for x in root)
            if refl == B: flat.add(pid)
print('panel roles forced flat by mirror face-to-face contacts:', len(flat), 'of', len(panels))
