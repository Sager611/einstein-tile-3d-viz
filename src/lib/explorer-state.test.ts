import { describe, expect, it } from 'vitest';
import {
  DEFAULT_SETTINGS,
  decodeSettings,
  encodeSettings,
  normalizeSettings,
  type ExplorerSettings,
} from './explorer-state';

describe('explorer state', () => {
  it('round-trips a non-default state through a share hash', () => {
    const settings: ExplorerSettings = {
      level: 5,
      spread: 0.75,
      slice: 0.4,
      relief: 1,
      showFeatures: true,
      showEdges: false,
      colorMode: 'orientation',
      autoRotate: true,
      hiddenGroups: ['families:0', 'orientation:2'],
    };

    expect(decodeSettings(encodeSettings(settings))).toEqual(settings);
  });

  it('clamps malformed values and guards types', () => {
    const decoded = decodeSettings(
      '#level=9.7&spread=-2&slice=0&relief=NaN&features=yes&edges=0&color=invalid&rotate=1&hidden=families%3A0%2Cfamilies%3A0%2Corientation%3A24%2Cporcelain%3A1',
    );

    expect(decoded).toEqual({
      level: 5,
      spread: 0,
      slice: 0.1,
      relief: 1,
      showFeatures: false,
      showEdges: false,
      colorMode: 'orientation',
      autoRotate: true,
      hiddenGroups: ['families:0'],
    });

    expect(normalizeSettings({ level: 0, relief: 80 })).toMatchObject({ level: 0, relief: 80 });
    expect(normalizeSettings({ level: 3, relief: 24 }).relief).toBe(24);
  });

  it('normalizes hidden groups by key and keeps them across color modes', () => {
    const normalized = normalizeSettings({
      colorMode: 'families',
      hiddenGroups: ['orientation:2', 'families:0', 'families:0', 'porcelain:0', 'families:8', 'invalid'],
    });

    expect(normalized.hiddenGroups).toEqual(['families:0', 'orientation:2', 'porcelain:0']);
    expect(normalizeSettings({ ...normalized, colorMode: 'orientation' }).hiddenGroups).toEqual(normalized.hiddenGroups);
  });

  it('uses defaults for empty and incomplete hashes', () => {
    expect(decodeSettings('')).toEqual(DEFAULT_SETTINGS);
    expect(decodeSettings('#level=&spread=&slice=&relief=')).toEqual(DEFAULT_SETTINGS);
    expect(decodeSettings('#color=orientation')).toMatchObject({ hiddenGroups: [] });
  });

  it('defaults old links to rotation colors', () => {
    expect(decodeSettings('#level=2&color=porcelain').colorMode).toBe('orientation');
    expect(decodeSettings('#level=2&color=families').colorMode).toBe('orientation');
    expect(decodeSettings('#colors=families').colorMode).toBe('families');
  });
});
