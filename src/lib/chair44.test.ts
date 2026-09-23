import { getTiles, occupiedVoxels, panels, transformPoint, rotateVector, type Vec3 } from './chair44';
import { describe, it, expect } from 'vitest';

const distance = (a: Vec3, b: Vec3) =>
  Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]);
const keyPoint = (v: Vec3) => v.map((x) => Math.round(x * 10000)).join(',');

describe('chair44 geometry', () => {
  it('contains the expected panel features', () => {
    const features = panels.flatMap((panel) =>
      panel.features.map((feature) => ({ center: feature.center, feature })),
    );
    expect(panels).toHaveLength(24);
    expect(features).toHaveLength(192);
    for (const { center, feature } of features) {
      expect(Number.isInteger(feature.coefficient)).toBe(true);
      expect(Math.abs(feature.coefficient)).toBeGreaterThanOrEqual(1);
      expect(Math.abs(feature.coefficient)).toBeLessThanOrEqual(12);
      expect(distance(center, feature.apex)).toBeCloseTo(Math.abs(feature.coefficient) / 10000, 10);
    }
  });

  it.each(Array.from({ length: 12 }, (_, index) => index + 1))(
    'has eight positive and eight negative features at magnitude %i',
    (magnitude) => {
      const coefficients = panels.flatMap((panel) =>
        panel.features.map((feature) => feature.coefficient),
      );
      expect(coefficients.filter((coefficient) => coefficient === magnitude)).toHaveLength(8);
      expect(coefficients.filter((coefficient) => coefficient === -magnitude)).toHaveLength(8);
    },
  );

  it('tiles the expected voxels', () => {
    for (let level = 0; level <= 5; level++) {
      const tiles = getTiles(level);
      expect(tiles).toHaveLength(8 ** level);
      const voxels = tiles.flatMap((tile) => occupiedVoxels(tile));
      const actual = new Set(voxels.map(([x, y, z]) => `${x},${y},${z}`));
      const size = 2 ** level;
      const expected = new Set<string>();
      for (let x = 0; x < 2 * size; x++) {
        for (let y = 0; y < 2 * size; y++) {
          for (let z = 0; z < 2 * size; z++) {
            if (x < size || y < size || z < size) expected.add(`${x},${y},${z}`);
          }
        }
      }
      expect(actual).toHaveLength(7 * 8 ** level);
      expect(actual).toEqual(expected);
    }
  });

  it('builds all 262,144 level-6 placements', () => {
    expect(getTiles(6)).toHaveLength(8 ** 6);
  });

  it.each([1, 2, 3])('matches all level-%i panel contacts', (level) => {
    const transformed = getTiles(level).flatMap((tile) =>
      panels.map((panel) => ({
        center: transformPoint(panel.center, tile),
        normal: rotateVector(panel.normal, tile),
        features: panel.features.map((feature) => ({
          base: feature.base.map((point) => transformPoint(point, tile)),
          apex: transformPoint(feature.apex, tile),
        })),
      })),
    );
    const groups = new Map<string, typeof transformed>();
    for (const panel of transformed) {
      const group = groups.get(keyPoint(panel.center)) ?? [];
      group.push(panel);
      groups.set(keyPoint(panel.center), group);
    }
    let pairedPanels = 0;
    let pairedFeatures = 0;
    for (const group of groups.values()) {
      expect(group.length).toBeLessThanOrEqual(2);
      if (group.length !== 2) continue;
      const [a, b] = group;
      expect(b.normal.every((component, index) => component === -a.normal[index])).toBe(true);
      const signature = (feature: (typeof a.features)[number]) =>
        `${feature.base.map(keyPoint).sort().join(';')}|${keyPoint(feature.apex)}`;
      expect(new Set(a.features.map(signature))).toEqual(new Set(b.features.map(signature)));
      pairedPanels += 1;
      pairedFeatures += a.features.length;
    }
    const expectedPairedPanels = 12 * (8 ** level - 4 ** level);
    expect(pairedPanels).toBe(expectedPairedPanels);
    expect(pairedFeatures).toBe(8 * expectedPairedPanels);
  });

  it('rejects invalid levels and is deterministic', () => {
    expect(() => getTiles(-1)).toThrow();
    expect(() => getTiles(1.5)).toThrow();
    expect(() => getTiles(7)).toThrow();
    expect(getTiles(3)).toEqual(getTiles(3));
  });
});
