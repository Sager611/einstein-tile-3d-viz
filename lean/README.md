# ChairWarp — Lean 4 proofs for an equivariant warp of Chair44

Build: `lake build` (Lean `v4.35.0-rc2`, Mathlib). Axiom audit: `lake env lean Axioms.lean`
→ every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`. No `sorry`,
`admit`, `native_decide`, or `axiom` declarations.

## Main theorem — `chair44_warp_concrete` (`ChairWarp/Final.lean`)

Let `Q ⊆ ℝ³` be Chair44, defined concretely in Lean from the paper's panel recipe (seven-cube
carrier, 192 square-pyramid bumps and dents). Let `T = (g i '' Q)` be a tiling of `ℝ³` by copies of
`Q` whose placements lie in Chair44's motion group `GammaGeom` and which has no nonzero translational
symmetry. Then for the explicit homeomorphism `warp : ℝ³ ≃ₜ ℝ³`:

1. `(g i '' warp '' Q)` is a tiling of `ℝ³` by congruent copies of the single solid `warp '' Q`;
2. `warp '' Q` has **no non-identity self-isometry** (`warp_rigid`);
3. the warped tiling has **no nonzero translational symmetry**;
4. the new solid genuinely differs from Chair44: `warp '' Q ≠ Q` (`warp_image_ne`).

## What is proved

| File | Content |
|---|---|
| `Transfer.lean` | General: an equivariant homeomorphism maps tilings to tilings; symmetries transfer under rigidity. |
| `Gamma.lean` | `Γ = R24 ⋉ BCC` is closed; hierarchy tiles and all 44 atlas contacts lie in `Γ`; face transitivity; face stabilizer. |
| `Geometry.lean` | Integer poses are isometries of `ℝ³`; composition matches; `GammaGeom` = generated subgroup. |
| `Warp.lean` | `field = ε ∑_{R∈R24} cos(2π k·Rx) R⁻¹e₁` (`k = (1,1/2,1/2)`, `e₁ = (1,1,0)`, `ε = 10⁻⁹`): lattice-periodic, rotation-equivariant, `1/5`-Lipschitz ⇒ `warp = id + field` is a homeomorphism commuting with `GammaGeom`; `‖warp x − x‖ ≤ 36ε`; exact certificate `warp (3/4,1/2,0) = (3/4,1/2,−4ε)` (the `√2` parts of the eighth-turn cosines cancel, checked by `decide`). The field is chiral: it has non-zero normal components on grid faces, so faces genuinely bend. |
| `Main.lean` | Symmetries in `Γ` transfer both ways; registration glue (`placements_mem`); generic main theorem. |
| `Tile.lean` | Chair44 `Q` as a subset of `ℝ³` (paper §2 hypograph definition); cover by 103 integer boxes; coordinate bounds; distance from `(2,2,2)`; corners in `Q`; 5 feature probes (height-12 bump over a dent) with `10⁻⁴` clearance — all box facts by `decide`. |
| `Diam.lean` | Points of `Q` almost `√12` apart sit at opposite box corners (not `0`, not `(2,2,2)`). |
| `Pin.lean` | Near-symmetries of `Q` map corners to corners, preserve integer squared distances exactly, are pinned to one of 12 box symmetries (`decide` over corner quadruples), are affinely close to it on the whole box; end-swapping symmetries are excluded via `(2,2,2)`, the 5 non-trivial axis permutations via the probes ⇒ `‖σ x − x‖ ≤ 300 d` (`near_id_on_box`). |
| `Ergodic.lean` | Mean ergodic theorem ⇒ an isometry all of whose powers stay within `C < 1/2` of the identity on a unit ball is the identity. |
| `Final.lean` | Every self-isometry of `warp '' Q` and all its powers are near-symmetries of `Q` with defect `72ε` ⇒ `warp_rigid`; `warp_image_ne` (the certificate point of the bottom face is pushed out of every box covering `Q`); `chair44_warp_concrete`. |

## Three infinite families (`ChairWarp/Family.lean`, `ChairWarp/FamilyFinal.lean`)

`WaveSpec` = integer data `(2k, e)`; `V(x) = Σ_{R ∈ R24} cos(2π k·Rx) R⁻¹e`, `Φ_s = id + sV`.
For any spec with small coefficients and even `2k₀+2k₁+2k₂` (`Good`, decided), and every
`0 ≤ s ≤ 10⁻⁹`: `Φ_s` is a homeomorphism commuting with `Γ` (`warp_comm`) and moves points by at
most `48 s`. `family_concrete`: given an integer certificate `Cert` (a point on Chair44's bottom face
pushed straight out, all `decide +kernel`), every `0 < s ≤ 10⁻⁹` gives a tiling solid that is rigid,
non-periodic and different from Chair44.

| Theorem | `k` | `e` | certificate point, `V` there |
|---|---|---|---|
| `familyA` | (1, ½, ½) | (1,1,0) | (¾, ½, 0), (0,0,−4) |
| `familyB` | (0, 2, 1) | (1,0,0) | (⅛, ¼, 0), (0,0,−4) |
| `familyC` | (3/2, 3/2, 1) | (1,0,0) | (¼, ½, 0), (0,0,−4) |

`Congruence.lean`: `congr_eq_one` — any isometry between two such warped tiles (any certified
waves, any amplitudes ≤ 10⁻⁹) is the identity (it must fix four convex corners of Chair44, where
every warped tile is a narrow cone). `familyA/B/C_noncongruent`: distinct amplitudes `s ≠ t` give
non-congruent solids, so **each family contains infinitely many pairwise non-congruent tiles**.
Not proved: that tiles from *different* families are non-congruent.

## Obstruction (`ChairWarp/Obstruction.lean`)

`equivariant_fixes_grid`: every map commuting with Chair44's motion group fixes every point of the
integer grid (`warp_fixes_grid` for the proved warp). Equivariant warps can bend faces and edges but can
never move a cube corner, so they cannot change the size of Chair44's arms.

## Hypotheses (from arXiv 2609.19214, Theorem 1.2)

* **Registration:** after one ambient isometry, neighbouring tiles differ by contacts of the atlas
  `A44`, which is proved here to lie in `Γ`; `placements_mem` then gives `hg`.
* **Non-periodicity:** `Per(T) = {0}`.

These are the paper's results about the unwarped Chair44 and are not re-proved here (the author's
own Lean development covers them). Everything specific to the warp is proved.

## Scope

The theorem describes warped Chair44 tilings. It does not claim that every tiling by `warp '' Q`
arises this way (that would require redoing the paper's registration argument for the warped solid).
