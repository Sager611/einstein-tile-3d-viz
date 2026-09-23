import { describe, expect, it } from 'vitest';
import { getTiles } from './chair44';
import {
  FAMILY_COLORS,
  PORCELAIN_COLOR,
  colorGroupKey,
  getLegendEntries,
  tileColor,
} from './color-groups';

describe('color groups', () => {
  it('assigns all 24 proper frames unique pastel colors, identity first', () => {
    const poses = getTiles(2);
    const frames = new Map<string, string>();
    for (const pose of poses) {
      const frame = `${pose.permutation.join(',')}|${pose.signs.join(',')}`;
      frames.set(frame, tileColor(pose, 'orientation'));
    }
    expect(frames.size).toBe(24);
    expect(new Set(frames.values()).size).toBe(24);
    expect(colorGroupKey(getTiles(0)[0], 'orientation')).toBe('orientation:0');
  });

  it('uses top-level family only and rotation only', () => {
    const poses = getTiles(2);
    const family0 = poses.filter((pose) => pose.lineage[0] === 0);
    expect(new Set(family0.map((pose) => tileColor(pose, 'families')))).toEqual(new Set([FAMILY_COLORS[0]]));

    const identity = poses.filter((pose) => pose.permutation.join(',') === '0,1,2' && pose.signs.join(',') === '1,1,1');
    expect(new Set(identity.map((pose) => tileColor(pose, 'orientation'))).size).toBe(1);
    expect(new Set(identity.map((pose) => pose.lineage[0])).size).toBeGreaterThan(1);
  });

  it('keeps porcelain uniform and counts every tile', () => {
    const poses = getTiles(2);
    expect(new Set(poses.map((pose) => tileColor(pose, 'porcelain')))).toEqual(new Set([PORCELAIN_COLOR]));
    for (const level of [1, 2]) {
      for (const mode of ['families', 'porcelain', 'orientation'] as const) {
        const entries = getLegendEntries(level, mode);
        expect(entries.length).toBeGreaterThan(0);
        expect(entries.reduce((sum, entry) => sum + entry.count, 0)).toBe(8 ** level);
        expect(entries.every((entry) => entry.count > 0)).toBe(true);
      }
    }
    expect(getLegendEntries(0, 'families')).toMatchObject([{ label: 'Family 1', count: 1 }]);
    expect(getLegendEntries(0, 'porcelain')).toMatchObject([{ label: 'Clay', count: 1 }]);
  });
});
