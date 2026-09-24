import sys; sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from gen import *
from a2b import carrier_cells
from a3 import all_cuttings
import a4
SF = [G for G in ALL48 if G[0] == (0, 1, 2)]
chair = carrier_cells(2, 2, 2, 1, 1, 1)
sols, car = all_cuttings(chair, (2, 2, 2), SF)
kids = [o[0] for o in sols[0]]
keep = [pid for pid in range(len(car.panels)) if pid not in a4.flat]
print('decorated panel roles:', keep)
car.slots = [s for s in car.slots if s[1] in keep]
car.S = len(car.slots)
car.setup()
r = car.evaluate(kids)
print({k: v for k, v in r.items() if k not in ('prof', 'A')})
