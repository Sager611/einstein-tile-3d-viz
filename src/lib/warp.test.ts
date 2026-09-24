import { describe, expect, it } from 'vitest';
import { getTiles, rotateVector, transformPoint, carrierCells, type Vec3 } from './chair44';
import { FACE_SHAPES, LEAN_CERTIFIED_AMOUNT, LEAN_MAX_SCALE, ROTATIONS, WARP_SHAPES, createWarpedChairGeometry, inBcc, leanField, safeAmplitude, shapeValue, warpDisplacement } from './warp';

const add = (a: Vec3, b: Vec3): Vec3 => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];

/** Random points on the exposed panels of the identity chair. */
function panelPoints(count: number, seed: number): Vec3[] {
  let state = seed;
  const random = () => ((state = (state * 16807) % 2147483647) / 2147483647);
  const cells = new Set(carrierCells.map((cell) => cell.join(',')));
  const points: Vec3[] = [];
  for (const cell of carrierCells) {
    for (let axis = 0; axis < 3; axis += 1) {
      for (const sign of [1, -1]) {
        const neighbour = [...cell] as Vec3;
        neighbour[axis] += sign;
        if (cells.has(neighbour.join(','))) continue;
        for (let k = 0; k < count; k += 1) {
          const p: Vec3 = [cell[0] + random(), cell[1] + random(), cell[2] + random()];
          p[axis] = cell[axis] + (sign > 0 ? 1 : 0);
          points.push(p);
        }
      }
    }
  }
  return points;
}

describe('equivariant face warps', () => {
  it('uses the 24 proper rotations and the body-centred lattice', () => {
    expect(ROTATIONS).toHaveLength(24);
    expect(inBcc([2, 0, -4])).toBe(true);
    expect(inBcc([1, -1, 3])).toBe(true);
    expect(inBcc([1, 0, 0])).toBe(false);
  });

  it('every tile pose in a level-2 block lies in Gamma = rotations x BCC', () => {
    for (const tile of getTiles(2)) expect(inBcc(tile.translation)).toBe(true);
  });

  it.each(FACE_SHAPES)('%s face shape is antisymmetric across the diagonal and vanishes on the boundary', (shape) => {
    for (const [u, v] of [[0.2, 0.7], [0.35, 0.1], [0.9, 0.45]]) {
      expect(shapeValue(shape, v, u)).toBeCloseTo(-shapeValue(shape, u, v), 12);
    }
    for (const t of [0, 0.3, 1]) {
      expect(shapeValue(shape, 0, t)).toBeCloseTo(0, 12);
      expect(shapeValue(shape, t, 1)).toBeCloseTo(0, 12);
    }
  });

  it.each(FACE_SHAPES)('%s at full amount keeps every face inside its double pyramid', (shape) => {
    const amplitude = safeAmplitude(shape);
    for (let i = 1; i < 200; i += 1) {
      for (let j = 1; j < 200; j += 1) {
        const u = i / 200, v = j / 200;
        expect(Math.abs(amplitude * shapeValue(shape, u, v))).toBeLessThan(Math.min(u, 1 - u, v, 1 - v));
      }
    }
  });

  it.each(WARP_SHAPES)('%s: every tile of a level-2 block is an exact copy of one warped tile', (shape) => {
    const warp = { shape, amount: 1 };
    const local = panelPoints(4, 11).map((p) => ({ p, warped: add(p, warpDisplacement(p, warp)) }));
    let worst = 0;
    for (const tile of getTiles(2)) {
      for (const { p, warped } of local) {
        const world = transformPoint(p, tile);
        const viaCopy = transformPoint(warped, tile);
        const viaGlobal = add(world, warpDisplacement(world, warp));
        worst = Math.max(worst, ...viaCopy.map((value, index) => Math.abs(value - viaGlobal[index])));
      }
    }
    expect(worst).toBeLessThan(1e-9);
  });

  it('builds the warped solid with volume exactly 7 (antisymmetric warps integrate to zero)', () => {
    const geometry = createWarpedChairGeometry({ shape: 'nubs', amount: 1 }, 8);
    const position = geometry.getAttribute('position');
    const index = geometry.getIndex();
    if (!index) throw new Error('expected indexed geometry');
    expect(index.count / 3).toBe(24 * 8 * 8 * 2);
    let volume = 0;
    for (let i = 0; i < index.count; i += 3) {
      const [a, b, c] = [0, 1, 2].map((k) => {
        const v = index.getX(i + k);
        return [position.getX(v), position.getY(v), position.getZ(v)];
      });
      volume += (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0]) + a[2] * (b[0] * c[1] - b[1] * c[0])) / 6;
    }
    expect(Math.abs(volume - 7)).toBeLessThan(1e-6); // Float32 vertex rounding
    // Rotations map normals consistently (sanity for the pose helpers).
    expect(rotateVector([0, 0, 1], getTiles(0)[0])).toEqual([0, 0, 1]);
  });

  it('the Lean warp field matches the Lean certificate V(3/4,1/2,0) = (0,0,-4)', () => {
    const v = leanField([0.75, 0.5, 0]);
    expect(v[0]).toBeCloseTo(0, 12);
    expect(v[1]).toBeCloseTo(0, 12);
    expect(v[2]).toBeCloseTo(-4, 12);
  });

  it('the Lean warp bends faces: normal components on grid faces are non-zero', () => {
    let worst = 0;
    for (let i = 1; i < 20; i += 1) for (let j = 1; j < 20; j += 1) {
      worst = Math.max(worst, Math.abs(leanField([i / 20, j / 20, 0])[2]));
    }
    expect(worst).toBeGreaterThan(3);
  });

  it('the certified range sits inside the displayed range', () => {
    expect(LEAN_CERTIFIED_AMOUNT).toBeGreaterThan(0.05);
    expect(LEAN_CERTIFIED_AMOUNT).toBeLessThan(1);
  });

  it('the displayed Lean warp stays a homeomorphism: sampled Lipschitz constant of s·V is below 1', () => {
    let state = 5;
    const random = () => ((state = (state * 16807) % 2147483647) / 2147483647);
    let worst = 0;
    for (let k = 0; k < 20000; k += 1) {
      const p: Vec3 = [2 * random(), 2 * random(), 2 * random()];
      const d: Vec3 = [1e-5 * (random() - 0.5), 1e-5 * (random() - 0.5), 1e-5 * (random() - 0.5)];
      const a = leanField(p), b = leanField(add(p, d));
      const num = Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]);
      worst = Math.max(worst, (LEAN_MAX_SCALE * num) / Math.hypot(...d));
    }
    expect(worst).toBeLessThan(1);
  });
});
