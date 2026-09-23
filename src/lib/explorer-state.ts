import { MAX_LEVEL } from './chair44';

export type ColorMode = 'families' | 'porcelain' | 'orientation';
export type ViewPreset = 'iso' | 'top' | 'front';

export const OVERVIEW_LEVEL = 4;

export interface ExplorerSettings {
  level: number;
  spread: number;
  slice: number;
  relief: number;
  showFeatures: boolean;
  showEdges: boolean;
  colorMode: ColorMode;
  autoRotate: boolean;
  hiddenGroups: string[];
}

export const DEFAULT_SETTINGS: ExplorerSettings = {
  level: 2,
  spread: 0.12,
  slice: 1,
  relief: 1,
  showFeatures: false,
  showEdges: true,
  colorMode: 'orientation',
  autoRotate: false,
  hiddenGroups: [],
};

export interface SceneHandle {
  reset(): void;
  setView(view: ViewPreset): void;
  zoom(factor: number): void;
  capture(): string | null;
  focus(): void;
}

const isFiniteNumber = (value: unknown): value is number =>
  typeof value === 'number' && Number.isFinite(value);

const clamp = (value: unknown, min: number, max: number, fallback: number): number => {
  const finiteValue = isFiniteNumber(value) ? value : fallback;
  return Math.min(max, Math.max(min, finiteValue));
};

const isColorMode = (value: unknown): value is ColorMode =>
  value === 'families' || value === 'porcelain' || value === 'orientation';

const validHiddenGroups = new Set([
  ...Array.from({ length: 8 }, (_, index) => `families:${index}`),
  ...Array.from({ length: 24 }, (_, index) => `orientation:${index}`),
  'porcelain:0',
]);

const normalizeHiddenGroups = (value: unknown): string[] =>
  Array.isArray(value)
    ? [...new Set(value.filter((group): group is string => typeof group === 'string' && validHiddenGroups.has(group)))].sort()
    : [];

export function normalizeSettings(input: Partial<ExplorerSettings>): ExplorerSettings {
  const source = input ?? {};
  const level = Math.round(clamp(source.level, 0, MAX_LEVEL, DEFAULT_SETTINGS.level));

  return {
    level,
    spread: clamp(source.spread, 0, 1, DEFAULT_SETTINGS.spread),
    slice: clamp(source.slice, 0.1, 1, DEFAULT_SETTINGS.slice),
    relief: clamp(source.relief, 1, 80, DEFAULT_SETTINGS.relief),
    showFeatures: typeof source.showFeatures === 'boolean' ? source.showFeatures : DEFAULT_SETTINGS.showFeatures,
    showEdges: typeof source.showEdges === 'boolean' ? source.showEdges : DEFAULT_SETTINGS.showEdges,
    colorMode: isColorMode(source.colorMode) ? source.colorMode : DEFAULT_SETTINGS.colorMode,
    autoRotate: typeof source.autoRotate === 'boolean' ? source.autoRotate : DEFAULT_SETTINGS.autoRotate,
    hiddenGroups: normalizeHiddenGroups(source.hiddenGroups),
  };
}

const settingKeys = {
  level: 'level',
  spread: 'spread',
  slice: 'slice',
  relief: 'relief',
  features: 'features',
  edges: 'edges',
  // v2 key: pre-rotation-default links used `color=` and are intentionally ignored.
  color: 'colors',
  rotate: 'rotate',
  hidden: 'hidden',
} as const;

export function encodeSettings(settings: ExplorerSettings): string {
  const normalized = normalizeSettings(settings);
  const params = new URLSearchParams({
    [settingKeys.level]: String(normalized.level),
    [settingKeys.spread]: String(normalized.spread),
    [settingKeys.slice]: String(normalized.slice),
    [settingKeys.relief]: String(normalized.relief),
    [settingKeys.features]: normalized.showFeatures ? '1' : '0',
    [settingKeys.edges]: normalized.showEdges ? '1' : '0',
    [settingKeys.color]: normalized.colorMode,
    [settingKeys.rotate]: normalized.autoRotate ? '1' : '0',
    [settingKeys.hidden]: normalized.hiddenGroups.join(','),
  });
  return `#${params.toString()}`;
}

const readNumber = (params: URLSearchParams, key: string): number | undefined => {
  const value = params.get(key);
  if (value === null || value.trim() === '') return undefined;
  const number = Number(value);
  return Number.isFinite(number) ? number : undefined;
};

const readBoolean = (params: URLSearchParams, key: string): boolean | undefined => {
  const value = params.get(key);
  if (value === '1') return true;
  if (value === '0') return false;
  return undefined;
};

const readColorMode = (params: URLSearchParams, key: string): ColorMode | undefined => {
  const value = params.get(key);
  return isColorMode(value) ? value : undefined;
};

const readHiddenGroups = (params: URLSearchParams, key: string): string[] | undefined => {
  const value = params.get(key);
  return value === null ? undefined : value.split(',');
};

export function decodeSettings(hash: string): ExplorerSettings {
  const query = typeof hash === 'string' ? hash.replace(/^#/, '') : '';
  const params = new URLSearchParams(query);

  return normalizeSettings({
    level: readNumber(params, settingKeys.level),
    spread: readNumber(params, settingKeys.spread),
    slice: readNumber(params, settingKeys.slice),
    relief: readNumber(params, settingKeys.relief),
    showFeatures: readBoolean(params, settingKeys.features),
    showEdges: readBoolean(params, settingKeys.edges),
    colorMode: readColorMode(params, settingKeys.color),
    autoRotate: readBoolean(params, settingKeys.rotate),
    hiddenGroups: readHiddenGroups(params, settingKeys.hidden),
  });
}
