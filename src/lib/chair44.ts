import definition from "../data/chair44-definition.json";

export type Vec3 = [number, number, number];
export interface TilePose { id: number; permutation: Vec3; signs: Vec3; translation: Vec3; lineage: number[]; }
export interface Feature { coefficient: number; base: Vec3[]; apex: Vec3; center: Vec3; }
export interface Panel { id: number; center: Vec3; normal: Vec3; features: Feature[]; }

export const FEATURE_COUNT = 192;
export const MAX_LEVEL = 5;

const tuple = (values: readonly number[]): Vec3 => [values[0], values[1], values[2]];
const normalize = (values: readonly number[]): Vec3 => {
  const scale = definition.coordinateScale;
  return [values[0] / scale, values[1] / scale, values[2] / scale];
};
const average = (points: Vec3[]): Vec3 => {
  let x = 0;
  let y = 0;
  let z = 0;
  for (const point of points) {
    x += point[0];
    y += point[1];
    z += point[2];
  }
  return [x / points.length, y / points.length, z / points.length];
};

export const panels: Panel[] = definition.panels.map((panel) => ({
  id: panel.id,
  center: normalize(panel.center),
  normal: tuple(panel.normal),
  features: panel.features.map((feature) => {
    const base = feature.base.map(normalize);
    return { coefficient: feature.coefficient, base, apex: normalize(feature.apex), center: average(base) };
  }),
}));

export const carrierCells: Vec3[] = definition.carrierCells.map(tuple);
export const children: TilePose[] = definition.children.map((child, id) => ({
  id,
  permutation: tuple(child.permutation),
  signs: tuple(child.signs),
  translation: tuple(child.translation),
  lineage: [id],
}));

const identity: TilePose = { id: 0, permutation: [0, 1, 2], signs: [1, 1, 1], translation: [0, 0, 0], lineage: [] };

export function rotateVector(v: Vec3, p: TilePose): Vec3 {
  return [p.signs[0] * v[p.permutation[0]], p.signs[1] * v[p.permutation[1]], p.signs[2] * v[p.permutation[2]]];
}

export function transformPoint(v: Vec3, p: TilePose): Vec3 {
  const rotated = rotateVector(v, p);
  return [rotated[0] + p.translation[0], rotated[1] + p.translation[1], rotated[2] + p.translation[2]];
}

export function occupiedVoxels(p: TilePose): Vec3[] {
  return carrierCells.map((cell): Vec3 => [
    p.translation[0] + p.signs[0] * (cell[p.permutation[0]] + (p.signs[0] < 0 ? 1 : 0)),
    p.translation[1] + p.signs[1] * (cell[p.permutation[1]] + (p.signs[1] < 0 ? 1 : 0)),
    p.translation[2] + p.signs[2] * (cell[p.permutation[2]] + (p.signs[2] < 0 ? 1 : 0)),
  ]);
}

const compose = (parent: TilePose, child: TilePose, childIndex: number): TilePose => {
  const offset = rotateVector(child.translation, parent);
  const permutation: Vec3 = [
    child.permutation[parent.permutation[0]],
    child.permutation[parent.permutation[1]],
    child.permutation[parent.permutation[2]],
  ];
  const signs: Vec3 = [
    parent.signs[0] * child.signs[parent.permutation[0]],
    parent.signs[1] * child.signs[parent.permutation[1]],
    parent.signs[2] * child.signs[parent.permutation[2]],
  ];
  return {
    id: parent.id * children.length + childIndex,
    permutation,
    signs,
    translation: [2 * parent.translation[0] + offset[0], 2 * parent.translation[1] + offset[1], 2 * parent.translation[2] + offset[2]],
    lineage: [...parent.lineage, childIndex],
  };
};

const levels: TilePose[][] = [[identity]];

const copyPose = (pose: TilePose): TilePose => ({
  id: pose.id,
  permutation: tuple(pose.permutation),
  signs: tuple(pose.signs),
  translation: tuple(pose.translation),
  lineage: [...pose.lineage],
});

export function getTiles(level: number): TilePose[] {
  if (!Number.isInteger(level) || level < 0 || level > MAX_LEVEL) {
    throw new RangeError(`level must be an integer from 0 to ${MAX_LEVEL}`);
  }
  while (levels.length <= level) {
    const previous = levels[levels.length - 1];
    levels.push(previous.flatMap((parent) => children.map((child, index) => compose(parent, child, index))));
  }
  return levels[level].map(copyPose);
}
