import { describe, expect, it } from 'vitest';
import { getTiles, rotateVector, transformPoint, carrierCells, type Vec3 } from './chair44';
import { FAMILIES, ROTATIONS, amplitude, WARP_SHAPES, createWarpedChairGeometry, familyField, inBcc, magnification, warpDisplacement } from './warp';

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

describe('Lean-proven warp families', () => {
  it('uses the 24 proper rotations and the body-centred lattice', () => {
    expect(ROTATIONS).toHaveLength(24);
    expect(inBcc([2, 0, -4])).toBe(true);
    expect(inBcc([1, -1, 3])).toBe(true);
    expect(inBcc([1, 0, 0])).toBe(false);
  });

  it('every tile pose in a level-2 block lies in Gamma = rotations x BCC', () => {
    for (const tile of getTiles(2)) expect(inBcc(tile.translation)).toBe(true);
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

  it('builds a closed warped solid of volume close to 7', () => {
    const geometry = createWarpedChairGeometry({ shape: 'b', amount: 1 }, 8);
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
    expect(Math.abs(volume - 7)).toBeLessThan(0.5);
    // Rotations map normals consistently (sanity for the pose helpers).
    expect(rotateVector([0, 0, 1], getTiles(0)[0])).toEqual([0, 0, 1]);
  });

  it.each(WARP_SHAPES)('%s: field matches the Lean certificate value', (shape) => {
    const { point, value } = FAMILIES[shape].certificate;
    const v = familyField(shape, point);
    for (let i = 0; i < 3; i += 1) expect(v[i]).toBeCloseTo(value[i], 12);
  });

  it.each(WARP_SHAPES)('%s: bends faces (normal component on a grid face is non-zero)', (shape) => {
    let worst = 0;
    for (let i = 1; i < 20; i += 1) for (let j = 1; j < 20; j += 1) {
      worst = Math.max(worst, Math.abs(familyField(shape, [i / 20, j / 20, 0])[2]));
    }
    expect(worst).toBeGreaterThan(3);
  });

  it('families look different: face fields are pairwise far from equal or opposite', () => {
    // Only grid faces shape the displayed tile, so compare the normal displacement on face z = 0.
    const samples: Vec3[] = [];
    for (let i = 0; i < 24; i += 1) for (let j = 0; j < 24; j += 1) samples.push([(i + 0.5) / 24, (j + 0.5) / 24, 0]);
    const face = WARP_SHAPES.map((shape) => samples.map((p) => familyField(shape, p)[2]));
    const dot = (u: number[], v: number[]) => u.reduce((sum, value, index) => sum + value * v[index], 0);
    for (let a = 0; a < face.length; a += 1) for (let b = a + 1; b < face.length; b += 1) {
      const correlation = dot(face[a], face[b]) / Math.sqrt(dot(face[a], face[a]) * dot(face[b], face[b]));
      expect(Math.abs(correlation)).toBeLessThan(0.5);
    }
  });

  it('families are pairwise different fields', () => {
    const p: Vec3 = [0.3, 0.7, 0.1];
    const [a, b, c] = WARP_SHAPES.map((shape) => familyField(shape, p));
    expect(Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2])).toBeGreaterThan(0.1);
    expect(Math.hypot(b[0] - c[0], b[1] - c[1], b[2] - c[2])).toBeGreaterThan(0.1);
  });

  it('slider amount maps to the proved amplitude and the view magnifies it by a fixed factor', () => {
    expect(amplitude(1)).toBe(1e-9);
    expect(amplitude(0.25)).toBeCloseTo(2.5e-10, 20);
    for (const shape of WARP_SHAPES) {
      const shown = warpDisplacement([0.3, 0.6, 0.2], { shape, amount: 0.4 });
      const exact = familyField(shape, [0.3, 0.6, 0.2]).map((v) => amplitude(0.4) * v);
      for (let i = 0; i < 3; i += 1) expect(shown[i]).toBeCloseTo(magnification(shape) * exact[i], 12);
    }
  });

  it.each(WARP_SHAPES)('%s: the magnified view stays a homeomorphism (sampled Lipschitz constant of s·V below 1)', (shape) => {
    let state = 5;
    const random = () => ((state = (state * 16807) % 2147483647) / 2147483647);
    let worst = 0;
    for (let k = 0; k < 20000; k += 1) {
      const p: Vec3 = [2 * random(), 2 * random(), 2 * random()];
      const d: Vec3 = [1e-5 * (random() - 0.5), 1e-5 * (random() - 0.5), 1e-5 * (random() - 0.5)];
      const a = familyField(shape, p), b = familyField(shape, add(p, d));
      const num = Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]);
      worst = Math.max(worst, (FAMILIES[shape].maxScale * num) / Math.hypot(...d));
    }
    expect(worst).toBeLessThan(1);
  });
});
