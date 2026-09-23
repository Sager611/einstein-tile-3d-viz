import { BufferGeometry, Vector3 } from 'three';
import { describe, expect, it } from 'vitest';
import { panels } from './chair44';
import {
  createCarrierEdges,
  createCarrierGeometry,
  createChairGeometry,
} from './geometry';

const pointKey = (point: Vector3): string =>
  [point.x, point.y, point.z].map((value) => Math.round(value * 1e8)).join(',');

const edgeKey = (first: string, second: string): string =>
  [first, second].sort().join('|');

function readPoint(geometry: BufferGeometry, index: number): Vector3 {
  return new Vector3().fromBufferAttribute(geometry.getAttribute('position'), index);
}

function signedVolume(geometry: BufferGeometry): number {
  let volume = 0;
  for (let index = 0; index < geometry.getAttribute('position').count; index += 3) {
    const a = readPoint(geometry, index);
    const b = readPoint(geometry, index + 1);
    const c = readPoint(geometry, index + 2);
    volume += a.dot(new Vector3().crossVectors(b, c)) / 6;
  }
  return volume;
}

function inspectSurface(geometry: BufferGeometry): {
  triangles: number;
  vertices: number;
  edges: Map<string, number>;
} {
  const position = geometry.getAttribute('position');
  const normals = geometry.getAttribute('normal');
  const vertices = new Set<string>();
  const edges = new Map<string, number>();

  expect(position.count % 3).toBe(0);
  expect(normals).toBeDefined();
  for (let index = 0; index < position.count; index += 1) {
    const point = readPoint(geometry, index);
    expect(Number.isFinite(point.x)).toBe(true);
    expect(Number.isFinite(point.y)).toBe(true);
    expect(Number.isFinite(point.z)).toBe(true);
    vertices.add(pointKey(point));

    const normal = new Vector3().fromBufferAttribute(normals, index);
    expect(Number.isFinite(normal.x)).toBe(true);
    expect(Number.isFinite(normal.y)).toBe(true);
    expect(Number.isFinite(normal.z)).toBe(true);
    expect(normal.length()).toBeCloseTo(1, 5);
  }

  for (let index = 0; index < position.count; index += 3) {
    const a = readPoint(geometry, index);
    const b = readPoint(geometry, index + 1);
    const c = readPoint(geometry, index + 2);
    const faceCross = new Vector3().crossVectors(
      new Vector3().subVectors(b, a),
      new Vector3().subVectors(c, a),
    );
    expect(faceCross.lengthSq()).toBeGreaterThan(0);

    const faceNormal = faceCross.normalize();
    const vertexNormal = new Vector3().fromBufferAttribute(normals, index);
    expect(vertexNormal.dot(faceNormal)).toBeGreaterThan(0.999);

    const points = [pointKey(a), pointKey(b), pointKey(c)];
    for (let edgeIndex = 0; edgeIndex < 3; edgeIndex += 1) {
      const key = edgeKey(points[edgeIndex], points[(edgeIndex + 1) % 3]);
      edges.set(key, (edges.get(key) ?? 0) + 1);
    }
  }

  return { triangles: position.count / 3, vertices: vertices.size, edges };
}

function distance(first: Vector3, second: Vector3): number {
  return first.distanceTo(second);
}

function reliefApexPairs(): Array<{ atOne: Vector3; atForty: Vector3 }> {
  return panels.flatMap((panel) =>
    panel.features.map((feature) => {
      const center = new Vector3(...feature.center);
      const atOne = new Vector3(...feature.apex);
      const atForty = atOne
        .clone()
        .sub(center)
        .multiplyScalar(40)
        .add(center);
      return { atOne, atForty };
    }),
  );
}

describe('chair geometry', () => {
  it('builds a finite, oriented, closed genus-zero surface', () => {
    const geometry = createChairGeometry();
    try {
      const surface = inspectSurface(geometry);
      expect(surface.triangles).toBe(4272);
      expect(surface.vertices).toBe(2138);
      expect([...surface.edges.values()].every((count) => count === 2)).toBe(true);
      expect(surface.vertices - surface.edges.size + surface.triangles).toBe(2);
      expect(signedVolume(geometry)).toBeCloseTo(7, 6);

      expect(geometry.groups).toHaveLength(2);
      const [body, features] = geometry.groups;
      expect(body.start).toBe(0);
      expect(body.count).toBeGreaterThan(0);
      expect(features.start).toBe(body.count);
      expect(features.count).toBeGreaterThan(0);
      expect(body.count + features.count).toBe(
        geometry.getAttribute('position').count,
      );
      expect(body.materialIndex).toBe(0);
      expect(features.materialIndex).toBe(1);
    } finally {
      geometry.dispose();
    }
  });

  it('keeps planar and base coordinates while changing only relief apexes', () => {
    const standard = createChairGeometry(1);
    const deep = createChairGeometry(40);
    try {
      const standardPosition = standard.getAttribute('position');
      const deepPosition = deep.getAttribute('position');
      expect(deepPosition.count).toBe(standardPosition.count);

      const apexPairs = reliefApexPairs();
      let unchanged = 0;
      let changed = 0;
      for (let index = 0; index < standardPosition.count; index += 1) {
        const first = readPoint(standard, index);
        const second = readPoint(deep, index);
        if (first.equals(second)) {
          unchanged += 1;
          continue;
        }
        changed += 1;
        expect(
          apexPairs.some(
            (pair) =>
              distance(first, pair.atOne) < 1e-6 &&
              distance(second, pair.atForty) < 1e-6,
          ),
        ).toBe(true);
      }
      expect(unchanged).toBeGreaterThan(0);
      expect(changed).toBeGreaterThan(0);
      expect(signedVolume(standard)).toBeCloseTo(7, 6);
      expect(signedVolume(deep)).toBeCloseTo(7, 6);
    } finally {
      standard.dispose();
      deep.dispose();
    }
  });

  it('builds a finite, closed seven-cube carrier surface', () => {
    const carrier = createCarrierGeometry();
    try {
      const surface = inspectSurface(carrier);
      expect(surface.triangles).toBe(48);
      expect([...surface.edges.values()].every((count) => count === 2)).toBe(true);
      expect(surface.vertices - surface.edges.size + surface.triangles).toBe(2);
      expect(signedVolume(carrier)).toBeCloseTo(7, 6);
    } finally {
      carrier.dispose();
    }
  });

  it('builds finite carrier edges', () => {
    const carrier = createCarrierEdges();
    try {
      const position = carrier.getAttribute('position');
      expect(position.count).toBeGreaterThan(0);
      for (let index = 0; index < position.count; index += 1) {
        expect(Number.isFinite(position.getX(index))).toBe(true);
        expect(Number.isFinite(position.getY(index))).toBe(true);
        expect(Number.isFinite(position.getZ(index))).toBe(true);
      }
    } finally {
      carrier.dispose();
    }
  });
});
