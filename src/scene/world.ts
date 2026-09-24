import {
  BufferGeometry,
  CanvasTexture,
  Color,
  DynamicDrawUsage,
  Float32BufferAttribute,
  Group,
  InstancedMesh,
  LineBasicMaterial,
  LineSegments,
  Matrix4,
  Mesh,
  MeshStandardMaterial,
  Raycaster,
  SRGBColorSpace,
  Vector3,
} from "three";
import { getTiles, MAX_LEVEL, transformPoint, type TilePose } from "../lib/chair44";
import { colorGroupKey, SELECTED_COLOR, tileColor } from "../lib/color-groups";
import { createCarrierEdges, createCarrierGeometry, createChairGeometry } from "../lib/geometry";
import { OVERVIEW_LEVEL, type ExplorerSettings } from "../lib/explorer-state";
import { createWarpedChairGeometry } from "../lib/warp";

/** Exact tile geometry: the feature-decorated Chair44, or its equivariant face warp (features omitted). */
const exactKey = (settings: ExplorerSettings): string =>
  settings.warp > 0 ? `warp|${settings.warp}|${settings.warpShape}` : `flat|${settings.relief}`;
const exactGeometry = (settings: ExplorerSettings): BufferGeometry =>
  settings.warp > 0
    ? createWarpedChairGeometry({ shape: settings.warpShape, amount: settings.warp }, 16)
    : createChairGeometry(settings.relief);

const FEATURE_TINT = 0.62;
const OVERVIEW_TEXTURE_SIZE = 256;
const OVERVIEW_FEATURE_OFFSETS: readonly [number, number][] = [
  [-0.125, -0.25],
  [-0.125, 0.25],
  [0.125, -0.25],
  [0.125, 0.25],
  [-0.25, -0.125],
  [-0.25, 0.125],
  [0.25, -0.125],
  [0.25, 0.125],
];

function setFeatureColor(material: MeshStandardMaterial, baseColor: string, showFeatures: boolean): void {
  material.color.set(baseColor);
  if (!showFeatures) material.color.multiplyScalar(FEATURE_TINT);
}

function createOverviewTexture(): CanvasTexture | null {
  if (typeof document === "undefined") return null;
  const canvas = document.createElement("canvas");
  canvas.width = OVERVIEW_TEXTURE_SIZE;
  canvas.height = OVERVIEW_TEXTURE_SIZE;
  const context = canvas.getContext("2d");
  if (!context) return null;

  context.fillStyle = "#ffffff";
  context.fillRect(0, 0, OVERVIEW_TEXTURE_SIZE, OVERVIEW_TEXTURE_SIZE);
  const squareSize = 0.02 * OVERVIEW_TEXTURE_SIZE;
  context.fillStyle = "#9e9e9e";
  for (const [u, v] of OVERVIEW_FEATURE_OFFSETS) {
    const x = u * OVERVIEW_TEXTURE_SIZE - squareSize / 2;
    const y = (1 - v) * OVERVIEW_TEXTURE_SIZE - squareSize / 2;
    context.fillRect(x, y, squareSize, squareSize);
  }

  const texture = new CanvasTexture(canvas);
  texture.colorSpace = SRGBColorSpace;
  texture.anisotropy = 4;
  texture.generateMipmaps = true;
  return texture;
}

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

const colorCache = new Map<string, Color>();
// Parsing CSS colors per instance dominates level-6 updates; cache parsed values.
function cachedColor(css: string): Color {
  let color = colorCache.get(css);
  if (!color) { color = new Color(css); colorCache.set(css, color); }
  return color;
}

export class TileWorld {
  readonly root = new Group();
  readonly body: InstancedMesh;
  readonly lines: LineSegments;
  readonly selectedOutline: LineSegments;
  readonly selectedDetail: Mesh;
  extent = 0;
  visibleCount = 0;
  private readonly carrier = createCarrierEdges();
  private readonly idMap: number[] = [];
  private readonly matrices: Matrix4[] = [];
  private poses: TilePose[] = [];
  private level = -1;
  private geometryKey: string;
  private overviewKey = '';
  private readonly geometry: BufferGeometry;
  private readonly overviewGeometry = createCarrierGeometry();
  private readonly bodyMaterial: MeshStandardMaterial;
  private readonly overviewMaterial: MeshStandardMaterial;
  private readonly overviewTexture: CanvasTexture | null;
  private readonly featureMaterial: MeshStandardMaterial;
  private readonly selectedDetailFeatureMaterial: MeshStandardMaterial;
  private promotedId: number | null = null;
  private promotedIndex = -1;

  constructor(settings: ExplorerSettings) {
    this.geometryKey = exactKey(settings);
    this.geometry = exactGeometry(settings);
    const bodyMaterial = new MeshStandardMaterial({ color: "#ffffff", roughness: 0.8 });
    this.bodyMaterial = bodyMaterial;
    const featureMaterial = new MeshStandardMaterial({ vertexColors: settings.showFeatures, roughness: 0.8 });
    setFeatureColor(featureMaterial, "#ffffff", settings.showFeatures);
    this.featureMaterial = featureMaterial;
    const selectedDetailBodyMaterial = bodyMaterial.clone();
    selectedDetailBodyMaterial.color.set(SELECTED_COLOR);
    const selectedDetailFeatureMaterial = featureMaterial.clone();
    setFeatureColor(selectedDetailFeatureMaterial, SELECTED_COLOR, settings.showFeatures);
    this.selectedDetailFeatureMaterial = selectedDetailFeatureMaterial;
    this.selectedDetail = new Mesh(this.geometry, [selectedDetailBodyMaterial, selectedDetailFeatureMaterial]);
    this.selectedDetail.name = "selected-detail";
    this.selectedDetail.matrixAutoUpdate = false;
    this.selectedDetail.visible = false;
    this.selectedDetail.matrix.makeScale(0, 0, 0);
    this.selectedDetail.scale.setScalar(0);
    this.overviewTexture = createOverviewTexture();
    this.overviewMaterial = new MeshStandardMaterial({
      color: "#ffffff",
      map: this.overviewTexture,
      roughness: 0.8,
    });
    this.body = new InstancedMesh(this.geometry, [bodyMaterial, featureMaterial], 8 ** MAX_LEVEL);
    this.body.castShadow = this.body.receiveShadow = true;
    this.body.instanceMatrix.setUsage(DynamicDrawUsage);
    const lineMaterial = new LineBasicMaterial({ color: "#52636c", transparent: true, opacity: 0.18 });
    this.lines = new LineSegments(new BufferGeometry(), lineMaterial);
    this.lines.frustumCulled = false;
    const selectedMaterial = new LineBasicMaterial({ color: SELECTED_COLOR, transparent: true, opacity: 0.9 });
    this.selectedOutline = new LineSegments(new BufferGeometry(), selectedMaterial);
    this.selectedOutline.frustumCulled = false;
    this.selectedOutline.scale.setScalar(0);
    this.root.add(this.body, this.selectedDetail, this.lines, this.selectedOutline);
    this.update(settings, null);
  }

  update(settings: ExplorerSettings, selectedId: number | null): void {
    const overview = settings.level >= OVERVIEW_LEVEL;
    this.body.material = overview ? [this.overviewMaterial] : [this.bodyMaterial, this.featureMaterial];
    this.body.geometry = overview ? this.overviewGeometry : this.geometry;
    if (exactKey(settings) !== this.geometryKey) {
      const replacement = exactGeometry(settings);
      this.geometry.copy(replacement); replacement.dispose();
      this.geometryKey = exactKey(settings);
    }
    // Overview warp: coarse warped carrier up to level 5; level 6 stays flat for performance.
    const overviewKey = settings.warp > 0 && settings.level <= 5 ? `${settings.warp}|${settings.warpShape}` : '';
    if (overview && overviewKey !== this.overviewKey) {
      const replacement = overviewKey ? createWarpedChairGeometry({ shape: settings.warpShape, amount: settings.warp }, 3) : createCarrierGeometry();
      this.overviewGeometry.copy(replacement); replacement.dispose();
      this.overviewKey = overviewKey;
    }
    if (this.featureMaterial.vertexColors !== settings.showFeatures) {
      this.featureMaterial.vertexColors = settings.showFeatures;
      setFeatureColor(this.featureMaterial, "#ffffff", settings.showFeatures);
      this.featureMaterial.needsUpdate = true;
      this.selectedDetailFeatureMaterial.vertexColors = settings.showFeatures;
      setFeatureColor(this.selectedDetailFeatureMaterial, SELECTED_COLOR, settings.showFeatures);
      this.selectedDetailFeatureMaterial.needsUpdate = true;
    }
    this.body.castShadow = this.body.receiveShadow = !overview;
    if (settings.level !== this.level) { this.level = settings.level; this.poses = getTiles(this.level); }
    const half = 2 ** this.level;
    this.extent = 2 * half;
    this.idMap.length = this.visibleCount = 0;
    this.matrices.length = 0;
    const hiddenSet = new Set(settings.hiddenGroups);
    for (let id = 0; id < this.poses.length; id++) {
      const pose = this.poses[id];
      if (hiddenSet.has(colorGroupKey(pose, settings.colorMode))) continue;
      const matrix = tileMatrix(pose, half, settings.spread);
      const canonicalZ = transformPoint([1, 1, 1], pose)[2];
      if (canonicalZ > Math.max(1, this.extent * settings.slice)) continue;
      this.body.setMatrixAt(this.visibleCount, matrix);
      const color = selectedId === pose.id ? SELECTED_COLOR : tileColor(pose, settings.colorMode);
      this.body.setColorAt(this.visibleCount, cachedColor(color));
      this.idMap.push(id); this.matrices.push(matrix); this.visibleCount++;
    }
    this.body.count = this.visibleCount;
    if (this.body.instanceColor) this.body.instanceColor.needsUpdate = true;
    this.lines.visible = settings.showEdges && !overview;
    if (this.lines.visible) {
      this.lines.geometry.dispose(); this.lines.geometry = transformedEdges(this.carrier, this.matrices);
    }
    const visible = selectedId === null ? -1 : this.idMap.indexOf(selectedId);
    if (visible >= 0 && settings.showEdges) {
      this.selectedOutline.geometry.dispose(); this.selectedOutline.geometry = transformedEdges(this.carrier, [this.matrices[visible]]); this.selectedOutline.scale.setScalar(1);
    } else this.selectedOutline.scale.setScalar(0);
    if (overview && visible >= 0) {
      this.selectedDetail.visible = true;
      this.selectedDetail.matrix.copy(this.matrices[visible]);
      this.selectedDetail.matrixWorldNeedsUpdate = true;
      this.selectedDetail.scale.setScalar(1);
      this.promotedId = selectedId;
      this.promotedIndex = visible;
      this.body.setMatrixAt(visible, new Matrix4().makeScale(0, 0, 0));
    } else {
      this.selectedDetail.visible = false;
      this.selectedDetail.matrix.makeScale(0, 0, 0);
      this.selectedDetail.matrixWorldNeedsUpdate = true;
      this.selectedDetail.scale.setScalar(0);
      this.promotedId = null;
      this.promotedIndex = -1;
    }
    this.body.instanceMatrix.needsUpdate = true;
    this.body.computeBoundingBox(); this.body.computeBoundingSphere();
    this.lines.geometry.computeBoundingBox(); this.lines.geometry.computeBoundingSphere();
  }

  pick(raycaster: Raycaster): number | null {
    const bodyHit = raycaster.intersectObject(this.body, false).find((intersection) =>
      intersection.instanceId !== undefined &&
      intersection.instanceId < this.visibleCount &&
      intersection.instanceId !== this.promotedIndex,
    );
    const detailHit = this.selectedDetail.visible ? raycaster.intersectObject(this.selectedDetail, false)[0] : undefined;
    if (detailHit && (!bodyHit || detailHit.distance < bodyHit.distance)) return this.promotedId;
    return bodyHit?.instanceId === undefined ? null : this.idMap[bodyHit.instanceId];
  }
  tileCenter(id: number): Vector3 | null {
    const index = this.idMap.indexOf(id);
    if (index < 0) return null;
    return new Vector3(1, 1, 1).applyMatrix4(this.matrices[index]);
  }
  dispose(): void {
    this.geometry.dispose(); this.overviewGeometry.dispose(); this.carrier.dispose(); this.lines.geometry.dispose(); this.selectedOutline.geometry.dispose();
    this.overviewTexture?.dispose();
    for (const material of [this.bodyMaterial, this.featureMaterial, this.overviewMaterial, this.selectedDetail.material, this.lines.material, this.selectedOutline.material].flat()) material.dispose();
  }
}
