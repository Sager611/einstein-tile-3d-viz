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
      level: 0,
      spread: 0.75,
      slice: 0.4,
      relief: 24,
      showFeatures: true,
      showEdges: false,
      colorMode: 'orientation',
      autoRotate: true,
    };

    expect(decodeSettings(encodeSettings(settings))).toEqual(settings);
  });

  it('clamps malformed values, guards types, and forces relief for nested levels', () => {
    const decoded = decodeSettings(
      '#level=9.7&spread=-2&slice=0&relief=NaN&features=yes&edges=0&color=invalid&rotate=1',
    );

    expect(decoded).toEqual({
      level: 3,
      spread: 0,
      slice: 0.1,
      relief: 1,
      showFeatures: false,
      showEdges: false,
      colorMode: 'families',
      autoRotate: true,
    });

    expect(normalizeSettings({ level: 0, relief: 80 })).toMatchObject({ level: 0, relief: 80 });
    expect(normalizeSettings({ level: 2, relief: 80 }).relief).toBe(1);
  });

  it('uses defaults for empty and incomplete hashes', () => {
    expect(decodeSettings('')).toEqual(DEFAULT_SETTINGS);
    expect(decodeSettings('#level=&spread=&slice=&relief=')).toEqual(DEFAULT_SETTINGS);
  });
});
