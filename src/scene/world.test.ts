import { describe, expect, it } from "vitest";
import { InstancedMesh, Matrix4, Vector3 } from "three";
import { DEFAULT_SETTINGS } from "../lib/explorer-state";
import { getTiles, transformPoint } from "../lib/chair44";
import { TileWorld } from "./world";

type Vec3 = [number, number, number];

const vector = ([x, y, z]: Vec3): Vector3 => new Vector3(x, y, z);
const bodyOf = (world: TileWorld): InstancedMesh => {
  const body = world.root.children.find(
    (child): child is InstancedMesh => child instanceof InstancedMesh,
  );
  if (!body) throw new Error("TileWorld body is missing");
  return body;
};

describe("TileWorld", () => {
  it("writes GPU instance transforms without transposing them", () => {
    const settings = { ...DEFAULT_SETTINGS, level: 1, spread: 0, slice: 1 };
    const world = new TileWorld(settings);

    try {
      const body = bodyOf(world);
      expect(world.extent).toBe(4);
      expect(body.count).toBe(8);

      const source: Vec3 = [0.31, 0.72, 1.13];
      const matrix = new Matrix4();
      const actual = new Vector3();
      const half = new Vector3(2, 2, 2);

      for (const [id, pose] of getTiles(1).entries()) {
        body.getMatrixAt(id, matrix);
        expect(matrix.determinant()).toBeCloseTo(1, 6);

        actual.copy(vector(source)).applyMatrix4(matrix);
        const expected = vector(transformPoint(source, pose)).sub(half);
        expect(actual.x).toBeCloseTo(expected.x, 6);
        expect(actual.y).toBeCloseTo(expected.y, 6);
        expect(actual.z).toBeCloseTo(expected.z, 6);
      }
    } finally {
      world.dispose();
    }
  });

  it("updates level, spread, slice, and selected-tile focus", () => {
    const settings = { ...DEFAULT_SETTINGS, level: 1, spread: 0, slice: 1 };
    const world = new TileWorld(settings);

    try {
      const body = bodyOf(world);
      const expanded = { ...settings, level: 2, spread: 0.3, slice: 1 };
      world.update(expanded, 0);
      expect(world.extent).toBe(8);
      expect(body.count).toBe(64);
      expect(world.selectedOutline.scale.x).toBe(1);

      const source: Vec3 = [0.31, 0.72, 1.13];
      const id = 1;
      const pose = getTiles(2)[id];
      const matrix = new Matrix4();
      const actual = new Vector3().fromArray(source);
      const half = new Vector3(4, 4, 4);
      body.getMatrixAt(id, matrix);
      actual.applyMatrix4(matrix);
      const expected = vector(transformPoint(source, pose))
        .sub(half)
        .add(vector(transformPoint([1, 1, 1], pose)).sub(half).multiplyScalar(0.3));
      expect(actual.x).toBeCloseTo(expected.x, 6);
      expect(actual.y).toBeCloseTo(expected.y, 6);
      expect(actual.z).toBeCloseTo(expected.z, 6);

      const hidden = { ...expanded, slice: 0.1 };
      world.update(hidden, 0);
      expect(body.count).toBeGreaterThan(0);
      expect(body.count).toBeLessThan(64);
      let hiddenId: number | undefined;
      for (let id = 0; id < 64; id += 1) {
        world.update(hidden, id);
        if (world.selectedOutline.scale.x === 0) {
          hiddenId = id;
          break;
        }
      }
      expect(hiddenId).toBeDefined();
      expect(world.selectedOutline.scale.x).toBe(0);

      world.update({ ...settings, level: 0, spread: 0, slice: 0.1 }, 0);
      expect(body.count).toBe(1);
      expect(world.selectedOutline.scale.x).toBe(1);
    } finally {
      world.dispose();
    }
  });
});
