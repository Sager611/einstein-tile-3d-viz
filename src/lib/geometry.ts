import {
  BufferGeometry,
  EdgesGeometry,
  Float32BufferAttribute,
  Vector2,
  Vector3,
} from 'three';
import { panels, type Vec3 } from './chair44';

const WHITE = [1, 1, 1] as const;
const TEAL = [0.08, 0.72, 0.65] as const;
const CORAL = [0.98, 0.38, 0.44] as const;

type PlaneAxes = [number, number];

function getPlaneAxes(normal: Vec3): PlaneAxes {
  const axes: number[] = [];
  for (let index = 0; index < 3; index += 1) {
    if (Math.abs(normal[index]) < 1e-6) axes.push(index);
  }
  return [axes[0] ?? 0, axes[1] ?? 1];
}

function project(point: Vec3, center: Vec3, axes: PlaneAxes): Vector2 {
  return new Vector2(
    point[axes[0]] - center[axes[0]],
    point[axes[1]] - center[axes[1]],
  );
}

function lift(point: Vector2, center: Vec3, axes: PlaneAxes): Vector3 {
  const result = new Vector3(center[0], center[1], center[2]);
  result.setComponent(axes[0], point.x + center[axes[0]]);
  result.setComponent(axes[1], point.y + center[axes[1]]);
  return result;
}

function vector(point: Vec3): Vector3 {
  return new Vector3(point[0], point[1], point[2]);
}

function appendTriangle(
  positions: number[],
  colors: number[],
  a: Vector3,
  b: Vector3,
  c: Vector3,
  normal: Vec3,
  color: readonly [number, number, number],
): void {
  const cross = new Vector3().crossVectors(
    new Vector3().subVectors(b, a),
    new Vector3().subVectors(c, a),
  );
  let second = b;
  let third = c;
  if (cross.x * normal[0] + cross.y * normal[1] + cross.z * normal[2] < 0) {
    second = c;
    third = b;
  }
  positions.push(...a.toArray(), ...second.toArray(), ...third.toArray());
  for (let index = 0; index < 3; index += 1) colors.push(...color);
}

function appendTriangleWithUvs(
  positions: number[],
  colors: number[],
  uvs: number[],
  a: Vector3,
  b: Vector3,
  c: Vector3,
  normal: Vec3,
  color: readonly [number, number, number],
  uvA: readonly [number, number],
  uvB: readonly [number, number],
  uvC: readonly [number, number],
): void {
  const cross = new Vector3().crossVectors(
    new Vector3().subVectors(b, a),
    new Vector3().subVectors(c, a),
  );
  let second = b;
  let third = c;
  let secondUv = uvB;
  let thirdUv = uvC;
  if (cross.x * normal[0] + cross.y * normal[1] + cross.z * normal[2] < 0) {
    second = c;
    third = b;
    secondUv = uvC;
    thirdUv = uvB;
  }
  positions.push(...a.toArray(), ...second.toArray(), ...third.toArray());
  for (let index = 0; index < 3; index += 1) colors.push(...color);
  uvs.push(...uvA, ...secondUv, ...thirdUv);
}

function sortedFeatureCorners(
  feature: (typeof panels)[number]['features'][number],
  panelCenter: Vec3,
  axes: PlaneAxes,
): Vec3[] {
  const featureCenter = project(feature.center, panelCenter, axes);
  return [...feature.base].sort((first, second) => {
    const firstPoint = project(first, panelCenter, axes);
    const secondPoint = project(second, panelCenter, axes);
    const firstAngle = Math.atan2(
      firstPoint.y - featureCenter.y,
      firstPoint.x - featureCenter.x,
    );
    const secondAngle = Math.atan2(
      secondPoint.y - featureCenter.y,
      secondPoint.x - featureCenter.x,
    );
    return firstAngle - secondAngle;
  });
}

const outerRing = [
  new Vector2(-0.5, -0.5),
  new Vector2(0.5, -0.5),
  new Vector2(0.5, 0.5),
  new Vector2(-0.5, 0.5),
];

export function createChairGeometry(relief = 1): BufferGeometry {
  const bodyPositions: number[] = [];
  const bodyColors: number[] = [];
  const featurePositions: number[] = [];
  const featureColors: number[] = [];

  for (const panel of panels) {
    const axes = getPlaneAxes(panel.normal);
    const holes: Vector2[][] = [];
    const cornersByFeature: Vec3[][] = [];

    for (const feature of panel.features) {
      const corners = sortedFeatureCorners(feature, panel.center, axes);
      cornersByFeature.push(corners);
      holes.push(corners.map((corner) => project(corner, panel.center, axes)));
    }

    const uniqueSorted = (values: number[]): number[] => {
      const unique = new Map<number, number>();
      for (const value of values) unique.set(Math.round(value * 1e10), value);
      return [...unique.values()].sort((first, second) => first - second);
    };
    const holePoints = holes.flat();
    const xs = uniqueSorted([-0.5, 0.5, ...holePoints.map((point) => point.x)]);
    const ys = uniqueSorted([-0.5, 0.5, ...holePoints.map((point) => point.y)]);
    const holeBounds = holes.map((hole) => {
      const holeXs = hole.map((point) => point.x);
      const holeYs = hole.map((point) => point.y);
      return {
        minX: Math.min(...holeXs),
        maxX: Math.max(...holeXs),
        minY: Math.min(...holeYs),
        maxY: Math.max(...holeYs),
      };
    });

    for (let xIndex = 0; xIndex < xs.length - 1; xIndex += 1) {
      for (let yIndex = 0; yIndex < ys.length - 1; yIndex += 1) {
        const minX = xs[xIndex];
        const maxX = xs[xIndex + 1];
        const minY = ys[yIndex];
        const maxY = ys[yIndex + 1];
        const midpointX = (minX + maxX) / 2;
        const midpointY = (minY + maxY) / 2;
        if (
          holeBounds.some(
            ({ minX: holeMinX, maxX: holeMaxX, minY: holeMinY, maxY: holeMaxY }) =>
              holeMinX < midpointX &&
              midpointX < holeMaxX &&
              holeMinY < midpointY &&
              midpointY < holeMaxY,
          )
        ) {
          continue;
        }

        const lowerLeft = lift(new Vector2(minX, minY), panel.center, axes);
        const lowerRight = lift(new Vector2(maxX, minY), panel.center, axes);
        const upperRight = lift(new Vector2(maxX, maxY), panel.center, axes);
        const upperLeft = lift(new Vector2(minX, maxY), panel.center, axes);
        appendTriangle(
          bodyPositions,
          bodyColors,
          lowerLeft,
          lowerRight,
          upperRight,
          panel.normal,
          WHITE,
        );
        appendTriangle(
          bodyPositions,
          bodyColors,
          lowerLeft,
          upperRight,
          upperLeft,
          panel.normal,
          WHITE,
        );
      }
    }

    panel.features.forEach((feature, featureIndex) => {
      const corners = cornersByFeature[featureIndex];
      const apex = vector(feature.apex).sub(vector(feature.center)).multiplyScalar(relief).add(vector(feature.center));
      const color = feature.coefficient > 0 ? TEAL : CORAL;
      for (let cornerIndex = 0; cornerIndex < 4; cornerIndex += 1) {
        appendTriangle(
          featurePositions,
          featureColors,
          vector(corners[cornerIndex]),
          vector(corners[(cornerIndex + 1) % 4]),
          apex,
          panel.normal,
          color,
        );
      }
    });
  }

  const geometry = new BufferGeometry();
  geometry.setAttribute(
    'position',
    new Float32BufferAttribute([...bodyPositions, ...featurePositions], 3),
  );
  geometry.setAttribute(
    'color',
    new Float32BufferAttribute([...bodyColors, ...featureColors], 3),
  );
  const bodyVertexCount = bodyPositions.length / 3;
  const featureVertexCount = featurePositions.length / 3;
  geometry.addGroup(0, bodyVertexCount, 0);
  geometry.addGroup(bodyVertexCount, featureVertexCount, 1);
  geometry.computeVertexNormals();
  return geometry;
}

export function createCarrierGeometry(): BufferGeometry {
  const positions: number[] = [];
  const colors: number[] = [];
  const uvs: number[] = [];

  for (const panel of panels) {
    const axes = getPlaneAxes(panel.normal);
    const corners = outerRing.map((corner) => lift(corner, panel.center, axes));
    appendTriangleWithUvs(
      positions,
      colors,
      uvs,
      corners[0],
      corners[1],
      corners[2],
      panel.normal,
      WHITE,
      [0, 0],
      [1, 0],
      [1, 1],
    );
    appendTriangleWithUvs(
      positions,
      colors,
      uvs,
      corners[0],
      corners[2],
      corners[3],
      panel.normal,
      WHITE,
      [0, 0],
      [1, 1],
      [0, 1],
    );
  }

  const geometry = new BufferGeometry();
  geometry.setAttribute('position', new Float32BufferAttribute(positions, 3));
  geometry.setAttribute('color', new Float32BufferAttribute(colors, 3));
  geometry.setAttribute('uv', new Float32BufferAttribute(uvs, 2));
  geometry.addGroup(0, positions.length / 3, 0);
  geometry.computeVertexNormals();
  return geometry;
}

export function createCarrierEdges(): BufferGeometry {
  const carrier = createCarrierGeometry();
  try {
    return new EdgesGeometry(carrier, 20);
  } finally {
    carrier.dispose();
  }
}
