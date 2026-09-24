import { BufferGeometry, Float32BufferAttribute } from 'three';
import { carrierCells, type Vec3 } from './chair44';

/**
 * Lean-proven warp families of Chair44 (`lean/ChairWarp/Family.lean`, `FamilyFinal.lean`).
 *
 * Every Chair44 tiling places tiles by motions from Gamma = (24 proper cube rotations) x (BCC lattice).
 * For a wave w = (k, e) the field V_w(x) = Σ_{R ∈ R24} cos(2π k·Rx) R⁻¹e commutes with Gamma, so
 * Φ_s = id + s V_w maps every Chair44 tiling onto a tiling by congruent copies of Φ_s(Q). Lean proves,
 * for every 0 < s ≤ 10⁻⁹ and each family A, B, C: Φ_s is a homeomorphism, Φ_s(Q) tiles, is rigid, has
 * non-periodic warped Chair44 tilings, and differs from Chair44. A, B, C are examples of the general
 * theorem `WaveSpec.family_concrete`; any valid wave gives another family. The view magnifies s.
 */

export type WarpShape = 'a' | 'b' | 'c';
export const WARP_SHAPES: readonly WarpShape[] = ['a', 'b', 'c'];

type Family = {
  /** 2k as integers. */
  k2: [number, number, number];
  e: [number, number, number];
  /** Largest displayed scale: 0.8 / (sampled Lipschitz constant, rounded up), so the view stays injective. */
  maxScale: number;
  /** Certificate point pushed out of Chair44 (Lean `famX_cert`) and its exact field value. */
  certificate: { point: [number, number, number]; value: [number, number, number] };
};

export const FAMILIES: Record<WarpShape, Family> = {
  a: { k2: [2, 1, 1], e: [1, 1, 0], maxScale: 0.8 / 36, certificate: { point: [0.75, 0.5, 0], value: [0, 0, -4] } },
  b: { k2: [0, 4, 2], e: [1, 0, 0], maxScale: 0.8 / 96, certificate: { point: [0.125, 0.25, 0], value: [0, 0, -4] } },
  c: { k2: [3, 3, 2], e: [1, 0, 0], maxScale: 0.8 / 72, certificate: { point: [0.25, 0.5, 0], value: [0, 0, -4] } },
};

/** Largest amplitude covered by the Lean theorems. */
export const LEAN_EPS = 1e-9;

type Frame = { perm: Vec3; signs: Vec3 };

const PERMS: Vec3[] = [
  [0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0],
];

const parity = (perm: Vec3): number => {
  let inversions = 0;
  for (let i = 0; i < 3; i += 1) for (let j = i + 1; j < 3; j += 1) if (perm[i] > perm[j]) inversions += 1;
  return inversions % 2 === 0 ? 1 : -1;
};

/** The 24 proper rotations of the cube as signed permutations: G(x)_i = s_i x_{p_i}. */
export const ROTATIONS: Frame[] = PERMS.flatMap((perm) =>
  [-1, 1].flatMap((a) => [-1, 1].flatMap((b) => [-1, 1].map((c): Frame => ({ perm, signs: [a, b, c] })))),
).filter(({ perm, signs }) => parity(perm) * signs[0] * signs[1] * signs[2] === 1);

const apply = ({ perm, signs }: Frame, x: Vec3): Vec3 => [
  signs[0] * x[perm[0]],
  signs[1] * x[perm[1]],
  signs[2] * x[perm[2]],
];

const applyInverse = ({ perm, signs }: Frame, y: Vec3): Vec3 => {
  const x: Vec3 = [0, 0, 0];
  for (let i = 0; i < 3; i += 1) x[perm[i]] = signs[i] * y[i];
  return x;
};

/** Body-centred cubic: all coordinates even, or all odd. */
export const inBcc = (t: Vec3): boolean =>
  t.every((value) => value % 2 === 0) || t.every((value) => Math.abs(value % 2) === 1);

/** V_w(x) = Σ_R cos(2π k·Rx) R⁻¹e for family `shape`. */
export function familyField(shape: WarpShape, x: Vec3): Vec3 {
  const { k2, e } = FAMILIES[shape];
  const out: Vec3 = [0, 0, 0];
  for (const frame of ROTATIONS) {
    const y = apply(frame, x);
    const wave = Math.cos(Math.PI * (k2[0] * y[0] + k2[1] * y[1] + k2[2] * y[2]));
    const direction = applyInverse(frame, e);
    for (let i = 0; i < 3; i += 1) out[i] += wave * direction[i];
  }
  return out;
}

/** The slider picks the proved amplitude s = amount · 10⁻⁹ (each s is a distinct proved tile). */
export const amplitude = (amount: number): number => amount * LEAN_EPS;

/** Fixed display magnification of a family: displacement shown = magnification · s · V. */
export const magnification = (shape: WarpShape): number => FAMILIES[shape].maxScale / LEAN_EPS;

export type Warp = { shape: WarpShape; amount: number };

/** Displayed displacement Φ(y) - y: the proved field at scale `amount · maxScale`. */
export function warpDisplacement(y: Vec3, warp: Warp): Vec3 {
  if (warp.amount === 0) return [0, 0, 0];
  const v = familyField(warp.shape, y);
  const scale = warp.amount * FAMILIES[warp.shape].maxScale;
  return [scale * v[0], scale * v[1], scale * v[2]];
}

/**
 * The warped carrier Phi(Q) (features omitted): each exposed panel as an N x N displaced grid.
 * Indexed per panel, so shading is smooth across a face and stays crisp along cube edges.
 */
export function createWarpedChairGeometry(warp: Warp, segments = 16): BufferGeometry {
  const cells = new Set(carrierCells.map((cell) => cell.join(',')));
  const positions: number[] = [];
  const uvs: number[] = [];
  const indices: number[] = [];
  for (const cell of carrierCells) {
    for (let axis = 0; axis < 3; axis += 1) {
      for (const sign of [1, -1]) {
        const neighbour = [...cell] as Vec3;
        neighbour[axis] += sign;
        if (cells.has(neighbour.join(','))) continue;
        const [a, b] = [0, 1, 2].filter((index) => index !== axis);
        const base = positions.length / 3;
        for (let i = 0; i <= segments; i += 1) {
          for (let j = 0; j <= segments; j += 1) {
            const p = [...cell] as Vec3;
            p[axis] = cell[axis] + (sign > 0 ? 1 : 0);
            p[a] = cell[a] + i / segments;
            p[b] = cell[b] + j / segments;
            const d = warpDisplacement(p, warp);
            positions.push(p[0] + d[0], p[1] + d[1], p[2] + d[2]);
            uvs.push(i / segments, j / segments);
          }
        }
        // Outward orientation: (e_a x e_b) points along +axis iff (a,b,axis) is a cyclic order.
        const flip = (sign > 0) !== ((a + 1) % 3 === b);
        const at = (i: number, j: number) => base + i * (segments + 1) + j;
        for (let i = 0; i < segments; i += 1) {
          for (let j = 0; j < segments; j += 1) {
            const q = [at(i, j), at(i + 1, j), at(i + 1, j + 1), at(i, j + 1)];
            const order = flip ? [0, 2, 1, 0, 3, 2] : [0, 1, 2, 0, 2, 3];
            for (const k of order) indices.push(q[k]);
          }
        }
      }
    }
  }
  const geometry = new BufferGeometry();
  geometry.setIndex(indices);
  geometry.setAttribute('position', new Float32BufferAttribute(positions, 3));
  geometry.setAttribute('uv', new Float32BufferAttribute(uvs, 2));
  geometry.setAttribute('color', new Float32BufferAttribute(new Float32Array(positions.length).fill(1), 3));
  geometry.computeVertexNormals();
  geometry.addGroup(0, indices.length, 0);
  geometry.computeBoundingBox();
  geometry.computeBoundingSphere();
  return geometry;
}
