import { BufferGeometry, Float32BufferAttribute } from 'three';
import { carrierCells, type Vec3 } from './chair44';

/**
 * Equivariant face warps of Chair44.
 *
 * Every Chair44 tiling places tiles by motions from Gamma = (24 proper cube rotations) x (BCC lattice),
 * the space group I432 (verified: the 44-contact atlas generates exactly these motions). Gamma acts
 * transitively on unit grid faces, and the reference face F0 = [0,1]^2 x {0} is fixed only by the
 * half-turn (x,y,z) -> (y,x,-z). Hence any face function f with f(v,u) = -f(u,v) defines a global
 * Gamma-equivariant map Phi. Phi(gQ) = g Phi(Q), so Phi maps every Chair44 tiling onto a tiling by
 * congruent copies of the single warped solid Phi(Q). Keeping |f| below the distance to the face
 * boundary keeps each face inside the double pyramid to the neighbouring cube centres, so Phi is a
 * homeomorphism and the warped pieces still tile.
 */

export type WarpShape = 'lean' | 'nubs' | 'wave' | 'ridge';
export const WARP_SHAPES: readonly WarpShape[] = ['lean', 'nubs', 'wave', 'ridge'];
/** Face-local illustrative shapes (everything except the Lean-verified global warp). */
export const FACE_SHAPES: readonly Exclude<WarpShape, 'lean'>[] = ['nubs', 'wave', 'ridge'];

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

const REFERENCE_CENTRE2: Vec3 = [1, 1, 0]; // doubled centre of F0

/** A motion (G, t) in Gamma carrying the reference face F0 onto the grid face with doubled centre `centre2`. */
export function motionToFace(centre2: Vec3): { frame: Frame; translation: Vec3 } {
  for (const frame of ROTATIONS) {
    const image = apply(frame, REFERENCE_CENTRE2);
    const delta = image.map((value, index) => centre2[index] - value);
    if (delta.some((value) => value % 2 !== 0)) continue;
    const translation = delta.map((value) => value / 2) as Vec3;
    if (inBcc(translation)) return { frame, translation };
  }
  throw new Error(`no Gamma motion reaches face ${centre2.join(',')}`);
}

const bump = (u: number, v: number, cu: number, cv: number, sigma: number) =>
  Math.exp(-((u - cu) ** 2 + (v - cv) ** 2) / (2 * sigma * sigma));

/**
 * The warp proved in Lean (`lean/ChairWarp/Warp.lean`): V(x) = Σ_{R ∈ R24} cos(2π k·Rx) R⁻¹e₁ with
 * k = (1, 1/2, 1/2) and e₁ = (1, 1, 0). Lean uses Φ = id + ε V with ε = 10⁻⁹, proves Lip(V) ≤ 144π
 * (so Φ = id + s V is a homeomorphism for every s < 1/(144π), `LEAN_CERTIFIED_SCALE`), and proves
 * Φ(Q) ≠ Q: V(3/4, 1/2, 0) = (0, 0, -4) pushes that point of the bottom face out of the solid.
 * The slider goes further, to `LEAN_MAX_SCALE` = 0.8/36: V's sampled Lipschitz constant is about 35,
 * so s·V stays a contraction there, but that range is checked numerically only.
 */
export const LEAN_EPS = 1e-9;
export const LEAN_CERTIFIED_SCALE = 0.95 / (144 * Math.PI);
export const LEAN_MAX_SCALE = 0.8 / 36;
/** Slider amount up to which the displayed warp is inside Lean's certified bound. */
export const LEAN_CERTIFIED_AMOUNT = LEAN_CERTIFIED_SCALE / LEAN_MAX_SCALE;

export function leanField(x: Vec3): Vec3 {
  const out: Vec3 = [0, 0, 0];
  for (const frame of ROTATIONS) {
    const y = apply(frame, x);
    const wave = Math.cos(2 * Math.PI * (y[0] + (y[1] + y[2]) / 2));
    const direction = applyInverse(frame, [1, 1, 0]);
    for (let i = 0; i < 3; i += 1) out[i] += wave * direction[i];
  }
  return out;
}

/** Magnification of the displayed Lean warp relative to the proved one. */
export const leanMagnification = (amount: number): number => (amount * LEAN_MAX_SCALE) / LEAN_EPS;

/** Unit-amplitude antisymmetric face shapes on [0,1]^2 (vanish on the boundary, s(v,u) = -s(u,v)). */
export function shapeValue(shape: Exclude<WarpShape, 'lean'>, u: number, v: number): number {
  const window = Math.sin(Math.PI * u) * Math.sin(Math.PI * v);
  switch (shape) {
    case 'wave':
      return window * Math.sin(Math.PI * (u - v));
    case 'nubs':
      return window * (bump(u, v, 0.34, 0.66, 0.12) - bump(u, v, 0.66, 0.34, 0.12));
    case 'ridge':
      return window * Math.tanh(6 * (u - v));
  }
}

const SAMPLES = 96;
const safeAmplitudeCache = new Map<Exclude<WarpShape, 'lean'>, number>();

/** Largest amplitude keeping |A s| strictly inside the face's double pyramid (5% safety margin). */
export function safeAmplitude(shape: Exclude<WarpShape, 'lean'>): number {
  const cached = safeAmplitudeCache.get(shape);
  if (cached !== undefined) return cached;
  let best = Infinity;
  for (let i = 1; i < SAMPLES; i += 1) {
    for (let j = 1; j < SAMPLES; j += 1) {
      const u = i / SAMPLES, v = j / SAMPLES;
      const s = Math.abs(shapeValue(shape, u, v));
      if (s > 1e-9) best = Math.min(best, Math.min(u, 1 - u, v, 1 - v) / s);
    }
  }
  const amplitude = 0.95 * best;
  safeAmplitudeCache.set(shape, amplitude);
  return amplitude;
}

export type Warp = { shape: WarpShape; amount: number };

/** Displacement of a point `y` lying on a grid face (world coordinates, integer grid). */
export function warpDisplacement(y: Vec3, warp: Warp): Vec3 {
  if (warp.amount === 0) return [0, 0, 0];
  if (warp.shape === 'lean') {
    // Global warp: moves every point, including edges and corners.
    const v = leanField(y);
    const scale = warp.amount * LEAN_MAX_SCALE;
    return [scale * v[0], scale * v[1], scale * v[2]];
  }
  const faceShape = warp.shape;
  const onGrid = y.map((value) => Math.abs(value - Math.round(value)) < 1e-9);
  const axis = onGrid.filter(Boolean).length === 1 ? onGrid.indexOf(true) : -1;
  if (axis < 0) return [0, 0, 0]; // edges and corners never move
  const centre2 = y.map((value, index) => (index === axis ? 2 * Math.round(value) : 2 * Math.floor(value) + 1)) as Vec3;
  const { frame, translation } = motionToFace(centre2);
  const local = applyInverse(frame, [y[0] - translation[0], y[1] - translation[1], y[2] - translation[2]]);
  const height = warp.amount * safeAmplitude(faceShape) * shapeValue(faceShape, local[0], local[1]);
  return apply(frame, [0, 0, height]);
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
