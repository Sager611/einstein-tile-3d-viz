import { getTiles, type TilePose, type Vec3 } from './chair44';
import type { ColorMode } from './explorer-state';

export const FAMILY_COLORS = [
  '#9db9c6',
  '#c1cbbb',
  '#ddc9a9',
  '#bcb4ce',
  '#d5aba1',
  '#afc9c8',
  '#c7cbd3',
  '#d2c2b5',
] as const;
export const PORCELAIN_COLOR = '#e9e4db';
export const SELECTED_COLOR = '#edcb8d';

export interface ColorGroupEntry {
  key: string;
  label: string;
  color: string;
  description: string;
  count: number;
}

type OrientationFrame = {
  permutation: Vec3;
  signs: Vec3;
};

const AXES = ['x', 'y', 'z'] as const;
const SIGN_VALUES = [1, -1] as const;
const PERMUTATIONS: Vec3[] = [
  [0, 1, 2],
  [0, 2, 1],
  [1, 0, 2],
  [1, 2, 0],
  [2, 0, 1],
  [2, 1, 0],
];

function permutationParity(permutation: Vec3): number {
  let inversions = 0;
  for (let first = 0; first < 3; first += 1) {
    for (let second = first + 1; second < 3; second += 1) {
      if (permutation[first] > permutation[second]) inversions += 1;
    }
  }
  return inversions % 2 === 0 ? 1 : -1;
}

function frameDeterminant(frame: OrientationFrame): number {
  return permutationParity(frame.permutation) * frame.signs[0] * frame.signs[1] * frame.signs[2];
}

function frameKey(frame: OrientationFrame): string {
  return `${frame.permutation.join(',')}|${frame.signs.join(',')}`;
}

const ORIENTATION_FRAMES: OrientationFrame[] = [];
for (const permutation of PERMUTATIONS) {
  for (const firstSign of SIGN_VALUES) {
    for (const secondSign of SIGN_VALUES) {
      for (const thirdSign of SIGN_VALUES) {
        const frame: OrientationFrame = {
          permutation: [...permutation],
          signs: [firstSign, secondSign, thirdSign],
        };
        if (frameDeterminant(frame) === 1) ORIENTATION_FRAMES.push(frame);
      }
    }
  }
}

const ORIENTATION_INDEX = new Map<string, number>();
ORIENTATION_FRAMES.forEach((frame, index) => ORIENTATION_INDEX.set(frameKey(frame), index));

const ORIENTATION_COLORS = ORIENTATION_FRAMES.map((_, index) => `hsl(${index * 15}, 48%, 78%)`);

function orientationIndex(pose: TilePose): number {
  return ORIENTATION_INDEX.get(frameKey(pose)) ?? 0;
}

function orientationDescription(frame: OrientationFrame): string {
  const mapping = AXES.map(
    (axis, index) => `${axis} <- ${frame.signs[index] > 0 ? '+' : '-'}${AXES[frame.permutation[index]]}`,
  ).join(', ');
  return `Permutation [${frame.permutation.join(', ')}], signs [${frame.signs.map((sign) => (sign > 0 ? '+1' : '-1')).join(', ')}]; ${mapping}; same color = same rotation.`;
}

export function colorGroupKey(pose: TilePose, mode: ColorMode): string {
  if (mode === 'porcelain') return 'porcelain:0';
  if (mode === 'families') return `families:${pose.lineage[0] ?? 0}`;
  return `orientation:${orientationIndex(pose)}`;
}

export function tileColor(pose: TilePose, mode: ColorMode): string {
  if (mode === 'porcelain') return PORCELAIN_COLOR;
  if (mode === 'families') return FAMILY_COLORS[pose.lineage[0] ?? 0] ?? FAMILY_COLORS[0];
  return ORIENTATION_COLORS[orientationIndex(pose)];
}

function familyEntries(): ColorGroupEntry[] {
  return FAMILY_COLORS.map((color, index) => ({
    key: `families:${index}`,
    label: `Family ${index + 1}`,
    color,
    description: `Top-level substitution branch ${index + 1}; all its descendants share this color.`,
    count: 0,
  }));
}

function orientationEntries(): ColorGroupEntry[] {
  return ORIENTATION_FRAMES.map((frame, index) => ({
    key: `orientation:${index}`,
    label: `Rotation ${index + 1}`,
    color: ORIENTATION_COLORS[index],
    description: orientationDescription(frame),
    count: 0,
  }));
}

function groupEntries(mode: ColorMode): ColorGroupEntry[] {
  if (mode === 'families') return familyEntries();
  if (mode === 'orientation') return orientationEntries();
  return [{
    key: 'porcelain:0',
    label: 'Clay',
    color: PORCELAIN_COLOR,
    description: 'Uniform clay.',
    count: 0,
  }];
}

const legendCache = new Map<string, ColorGroupEntry[]>();

export function getLegendEntries(level: number, mode: ColorMode): ColorGroupEntry[] {
  const cacheKey = `${level}:${mode}`;
  const cached = legendCache.get(cacheKey);
  if (cached) return cached.map((entry) => ({ ...entry }));

  const counts = new Map<string, number>();
  for (const pose of getTiles(level)) {
    const key = colorGroupKey(pose, mode);
    counts.set(key, (counts.get(key) ?? 0) + 1);
  }

  const entries = groupEntries(mode)
    .map((entry) => ({ ...entry, count: counts.get(entry.key) ?? 0 }))
    .filter((entry) => entry.count > 0);
  legendCache.set(cacheKey, entries);
  return entries.map((entry) => ({ ...entry }));
}
