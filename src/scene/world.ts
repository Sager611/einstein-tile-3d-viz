import {
  BufferGeometry,
  Color,
  Float32BufferAttribute,
  Group,
  InstancedMesh,
  LineBasicMaterial,
  LineSegments,
  Matrix4,
  MeshStandardMaterial,
  Raycaster,
  Vector3,
} from "three";
import { getTiles, transformPoint, type TilePose } from "../lib/chair44";
import { createCarrierEdges, createChairGeometry } from "../lib/geometry";
import type { ExplorerSettings } from "../lib/explorer-state";

const PORCELAIN = new Color("#e9e4db");
const PALETTE = ["#9db9c6", "#c1cbbb", "#ddc9a9", "#bcb4ce", "#d5aba1", "#afc9c8", "#c7cbd3", "#d2c2b5"];
const SELECTED = new Color("#edcb8d");

function point(value: number[] | Vector3): Vector3 {
  return value instanceof Vector3 ? value.clone() : new Vector3(value[0], value[1], value[2]);
}
function tileMatrix(pose: TilePose, half: number, spread: number): Matrix4 {
  const corner = point(transformPoint([1, 1, 1], pose));
  const t = point(pose.translation);
  const x = t.x - half + spread * (corner.x - half);
  const y = t.y - half + spread * (corner.y - half);
  const z = t.z - half + spread * (corner.z - half);
  const p = pose.permutation, s = pose.signs;
  return new Matrix4().set(
    p[0] === 0 ? s[0] : 0, p[0] === 1 ? s[0] : 0, p[0] === 2 ? s[0] : 0, x,
    p[1] === 0 ? s[1] : 0, p[1] === 1 ? s[1] : 0, p[1] === 2 ? s[1] : 0, y,
    p[2] === 0 ? s[2] : 0, p[2] === 1 ? s[2] : 0, p[2] === 2 ? s[2] : 0, z,
    0, 0, 0, 1,
  );
}
function transformedEdges(source: BufferGeometry, matrices: Matrix4[]): BufferGeometry {
  const input = source.getAttribute("position");
  const values: number[] = [];
  const v = new Vector3();
  for (const matrix of matrices) for (let i = 0; i < input.count; i++) {
    v.fromBufferAttribute(input, i).applyMatrix4(matrix);
    values.push(v.x, v.y, v.z);
  }
  const geometry = new BufferGeometry();
  geometry.setAttribute("position", new Float32BufferAttribute(values, 3));
  geometry.computeBoundingBox();
  geometry.computeBoundingSphere();
  return geometry;
}

export class TileWorld {
  readonly root = new Group();
  readonly body: InstancedMesh;
  readonly lines: LineSegments;
  readonly selectedOutline: LineSegments;
  extent = 0;
  visibleCount = 0;
  private readonly carrier = createCarrierEdges();
  private readonly idMap: number[] = [];
  private readonly matrices: Matrix4[] = [];
  private poses: TilePose[] = [];
  private level = -1;
  private relief: number;
  private readonly geometry: BufferGeometry;
  private readonly featureMaterial: MeshStandardMaterial;
  private currentSpread = 0;

  constructor(settings: ExplorerSettings) {
    this.relief = settings.relief;
    this.geometry = createChairGeometry(settings.relief);
    const bodyMaterial = new MeshStandardMaterial({ color: PORCELAIN, roughness: 0.8 });
    const featureMaterial = new MeshStandardMaterial({ vertexColors: true, roughness: 0.8 });
    featureMaterial.visible = settings.showFeatures;
    this.featureMaterial = featureMaterial;
    this.body = new InstancedMesh(this.geometry, [bodyMaterial, featureMaterial], 512);
    this.body.castShadow = this.body.receiveShadow = true;
    this.body.instanceMatrix.setUsage(35044);
    const lineMaterial = new LineBasicMaterial({ color: "#52636c", transparent: true, opacity: 0.18 });
    this.lines = new LineSegments(new BufferGeometry(), lineMaterial);
    this.lines.frustumCulled = false;
    const selectedMaterial = new LineBasicMaterial({ color: SELECTED, transparent: true, opacity: 0.9 });
    this.selectedOutline = new LineSegments(new BufferGeometry(), selectedMaterial);
    this.selectedOutline.frustumCulled = false;
    this.selectedOutline.scale.setScalar(0);
    this.root.add(this.body, this.lines, this.selectedOutline);
    this.update(settings, null);
  }

  update(settings: ExplorerSettings, selectedId: number | null): void {
    this.currentSpread = settings.spread;
    if (settings.relief !== this.relief) {
      const replacement = createChairGeometry(settings.relief);
      this.geometry.copy(replacement); replacement.dispose();
      this.relief = settings.relief;
    }
    this.featureMaterial.visible = settings.showFeatures;
    if (settings.level !== this.level) { this.level = settings.level; this.poses = getTiles(this.level); }
    const half = 2 ** this.level;
    this.extent = 2 * half;
    this.idMap.length = this.visibleCount = 0;
    this.matrices.length = 0;
    for (let id = 0; id < this.poses.length && this.visibleCount < 512; id++) {
      const pose = this.poses[id], matrix = tileMatrix(pose, half, settings.spread);
      const center = new Vector3(0, 0, 0).applyMatrix4(matrix);
      if (center.z > Math.max(1, this.extent * settings.slice)) continue;
      this.body.setMatrixAt(this.visibleCount, matrix);
      const family = pose.lineage?.[0] || 0;
      const orientation = (pose.permutation[0] * 3 + pose.permutation[1] * 5 + pose.signs.reduce((a, b) => a + b, 0)) & 7;
      this.body.setColorAt(this.visibleCount, new Color(PALETTE[(family + orientation) % PALETTE.length]));
      this.idMap.push(id); this.matrices.push(matrix); this.visibleCount++;
    }
    this.body.count = this.visibleCount;
    this.body.instanceMatrix.needsUpdate = true;
    if (this.body.instanceColor) this.body.instanceColor.needsUpdate = true;
    this.lines.geometry.dispose(); this.lines.geometry = transformedEdges(this.carrier, this.matrices);
    if (selectedId !== null) {
      const visible = this.idMap.indexOf(selectedId);
      if (visible >= 0) { this.selectedOutline.geometry.dispose(); this.selectedOutline.geometry = transformedEdges(this.carrier, [this.matrices[visible]]); this.selectedOutline.scale.setScalar(1); }
      else this.selectedOutline.scale.setScalar(0);
    } else this.selectedOutline.scale.setScalar(0);
    this.body.computeBoundingBox(); this.body.computeBoundingSphere();
    this.lines.geometry.computeBoundingBox(); this.lines.geometry.computeBoundingSphere();
  }

  pick(raycaster: Raycaster): number | null {
    const hit = raycaster.intersectObject(this.body, false)[0];
    return hit?.instanceId === undefined || hit.instanceId >= this.visibleCount ? null : this.idMap[hit.instanceId];
  }
  tileCenter(id: number): Vector3 | null {
    const index = this.idMap.indexOf(id);
    if (index < 0) return null;
    const half = 2 ** this.level;
    const transformed = point(transformPoint([half, half, half], this.poses[this.idMap[index]]));
    return transformed.addScalar(-half).multiplyScalar(1 + this.currentSpread);
  }
  dispose(): void {
    this.geometry.dispose(); this.carrier.dispose(); this.lines.geometry.dispose(); this.selectedOutline.geometry.dispose();
    for (const material of [this.body.material, this.lines.material, this.selectedOutline.material].flat()) material.dispose();
  }
}
