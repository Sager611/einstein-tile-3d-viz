import {
  ArrowHelper,
  BufferGeometry,
  CanvasTexture,
  Color,
  DoubleSide,
  DynamicDrawUsage,
  Float32BufferAttribute,
  Group,
  InstancedMesh,
  LineBasicMaterial,
  LineSegments,
  Matrix4,
  Mesh,
  MeshBasicMaterial,
  MeshStandardMaterial,
  Raycaster,
  SphereGeometry,
  TorusGeometry,
  SRGBColorSpace,
  Vector3,
} from "three";
import { getTiles, MAX_LEVEL, transformPoint, type TilePose, type Vec3 } from "../lib/chair44";
import { colorGroupKey, SELECTED_COLOR, tileColor } from "../lib/color-groups";
import { createCarrierEdges, createCarrierGeometry, createChairGeometry } from "../lib/geometry";
import { OVERVIEW_LEVEL, type ExplorerSettings } from "../lib/explorer-state";
import { createWarpedChairGeometry, FAMILIES, warpDisplacement } from "../lib/warp";

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

/** Four convex corners of Chair44 that every equivariant warp fixes (Lean `WaveSpec.corners`). */
const FIXED_CORNERS: readonly Vec3[] = [[0, 0, 0], [2, 0, 0], [0, 2, 0], [0, 0, 2]];
const PROOF_COLOR = "#dc2626";
const CORNER_COLOR = "#0f172a";
const DEFAULT_VIEW = new Vector3(6, 6, 5).normalize();

/**
 * Proof overlay on one tile: the flat Chair44 as a ghost, the certificate point that Lean proves is
 * pushed out of Chair44 (white = original position, red = warped, arrow = displacement), and the four
 * corners every warp fixes. Markers ignore depth so they stay visible through the tile.
 */
class ProofOverlay {
  readonly root = new Group();
  private readonly sphere = new SphereGeometry(1, 20, 14);
  private readonly materials: (MeshBasicMaterial | LineBasicMaterial)[] = [];
  private readonly ghost: Mesh;
  private readonly ghostEdges: LineSegments;
  private readonly basePoint: Mesh;
  private readonly warpedPoint: Mesh;
  private readonly arrow: ArrowHelper;
  private readonly ringGeometry: TorusGeometry;
  private readonly callout: Mesh;
  private key = "";

  constructor() {
    this.root.name = "proof-overlay";
    this.root.matrixAutoUpdate = false;
    this.root.visible = false;
    const ghostMaterial = new MeshBasicMaterial({ color: CORNER_COLOR, transparent: true, opacity: 0.08, depthWrite: false, side: DoubleSide });
    const edgeMaterial = new LineBasicMaterial({ color: CORNER_COLOR, transparent: true, opacity: 0.9, depthTest: false });
    this.materials.push(ghostMaterial, edgeMaterial);
    this.ghost = new Mesh(createCarrierGeometry(), ghostMaterial);
    this.ghostEdges = new LineSegments(createCarrierEdges(), edgeMaterial);
    this.ghostEdges.renderOrder = 10;
    this.basePoint = this.marker("#ffffff", 0.04, 11);
    this.warpedPoint = this.marker(PROOF_COLOR, 0.045, 12);
    this.arrow = new ArrowHelper(new Vector3(0, 0, -1), new Vector3(), 0.1, PROOF_COLOR);
    this.arrow.renderOrder = 12;
    this.arrow.traverse((object) => {
      const material = (object as Mesh).material;
      if (material instanceof MeshBasicMaterial || material instanceof LineBasicMaterial) {
        material.depthTest = false; material.transparent = true; this.materials.push(material);
      }
    });
    // Callout ring on the certificate face (z = 0 of cube (0,0,0)), so the short true arrow is easy to find.
    this.ringGeometry = new TorusGeometry(0.14, 0.009, 8, 64);
    const ringMaterial = new MeshBasicMaterial({ color: PROOF_COLOR, depthTest: false, transparent: true, opacity: 0.9 });
    this.materials.push(ringMaterial);
    this.callout = new Mesh(this.ringGeometry, ringMaterial);
    this.callout.renderOrder = 12;
    this.root.add(this.ghost, this.ghostEdges, this.callout, this.basePoint, this.warpedPoint, this.arrow);
    for (const corner of FIXED_CORNERS) {
      const ring = this.marker("#ffffff", 0.07, 11);
      const dot = this.marker(CORNER_COLOR, 0.045, 12);
      ring.position.set(...corner); dot.position.set(...corner);
      ring.name = dot.name = "fixed-corner";
      this.root.add(ring, dot);
    }
  }

  private marker(color: string, radius: number, order: number): Mesh {
    const material = new MeshBasicMaterial({ color, depthTest: false, transparent: true });
    this.materials.push(material);
    const mesh = new Mesh(this.sphere, material);
    mesh.scale.setScalar(radius);
    mesh.renderOrder = order;
    return mesh;
  }

  update(settings: ExplorerSettings, matrix: Matrix4 | null): void {
    this.root.visible = settings.proof && settings.warp > 0 && matrix !== null;
    if (!this.root.visible || matrix === null) return;
    const key = `${settings.warpShape}|${settings.warp}`;
    if (key !== this.key) {
      const { point } = FAMILIES[settings.warpShape].certificate;
      const d = warpDisplacement(point, { shape: settings.warpShape, amount: settings.warp });
      const base = new Vector3(...point);
      const offset = new Vector3(...d);
      this.basePoint.position.copy(base);
      this.callout.position.copy(base);
      this.warpedPoint.position.copy(base).add(offset);
      const length = Math.max(offset.length(), 1e-6);
      this.arrow.position.copy(base);
      this.arrow.setDirection(offset.clone().normalize());
      this.arrow.setLength(length, Math.min(0.5 * length, 0.06), Math.min(0.35 * length, 0.04));
      this.key = key;
    }
    this.root.matrix.copy(matrix);
    this.root.matrixWorldNeedsUpdate = true;
  }

  dispose(): void {
    this.sphere.dispose(); this.ringGeometry.dispose(); this.ghost.geometry.dispose(); this.ghostEdges.geometry.dispose();
    this.arrow.dispose();
    for (const material of this.materials) material.dispose();
  }
}

/** Index of the visible tile whose certificate face points at the default camera and sits outermost. */
function proofTileIndex(matrices: readonly Matrix4[], point: Vec3): number {
  let best = -1, bestScore = -Infinity;
  const p = new Vector3(), n = new Vector3();
  for (let i = 0; i < matrices.length; i++) {
    n.set(0, 0, -1).transformDirection(matrices[i]);
    if (n.dot(DEFAULT_VIEW) < 0.4) continue;
    const score = p.set(...point).applyMatrix4(matrices[i]).dot(DEFAULT_VIEW);
    if (score > bestScore) { bestScore = score; best = i; }
  }
  return best >= 0 ? best : matrices.length > 0 ? 0 : -1;
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
  private readonly proof = new ProofOverlay();
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
    this.root.add(this.body, this.selectedDetail, this.lines, this.selectedOutline, this.proof.root);
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
    const proofIndex = !settings.proof || settings.warp === 0 ? -1
      : visible >= 0 ? visible : proofTileIndex(this.matrices, FAMILIES[settings.warpShape].certificate.point);
    this.proof.update(settings, proofIndex >= 0 ? this.matrices[proofIndex] : null);
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
    this.proof.dispose();
    this.geometry.dispose(); this.overviewGeometry.dispose(); this.carrier.dispose(); this.lines.geometry.dispose(); this.selectedOutline.geometry.dispose();
    this.overviewTexture?.dispose();
    for (const material of [this.bodyMaterial, this.featureMaterial, this.overviewMaterial, this.selectedDetail.material, this.lines.material, this.selectedOutline.material].flat()) material.dispose();
  }
}
