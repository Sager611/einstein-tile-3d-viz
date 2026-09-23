# Geometry and provenance

This app uses an independent, finite-surface reconstruction of the proposed decorated chair geometry. It is a numerical reconstruction, not a copied upstream mesh or program, and the finite checks below are not a proof of an infinite tiling.

## Carrier and decorations

- **Carrier:** seven unit cubes from the `2 × 2 × 2` block, with the cube at `(1, 1, 1)` missing. Equivalently, the occupied cells are `(0,0,0)`, `(0,0,1)`, `(0,1,0)`, `(0,1,1)`, `(1,0,0)`, `(1,0,1)`, and `(1,1,0)`. Its exposed boundary has **24 unit-square panels**.
- **Panel features:** every panel has **8** features. In panel-local tangent coordinates `(u,v)` measured from the panel center, their centers are the eight points in `(±1/8, ±1/4)` and `(±1/4, ±1/8)` (independent sign choices).
- **Base:** each feature replaces a `1/50 × 1/50` square of its panel.
- **Apex:** the signed outward-normal height is `h = a/10000`, where `a ∈ {-12,…,-1,1,…,12}`. Positive `a` is an outward bump; negative `a` is an inward dent. The full surface has `24 × 8 = 192` features.

The independent AXIS-GRID mesh splits each of the 24 unit panels on all feature-base coordinate grid lines, skips the eight square holes in each panel, and caps each pyramid with four side triangles from its four base corners to its signed apex. Equal geometric vertices and shared panel edges are welded; triangle winding is chosen for the global outward boundary orientation. This is an independent triangulation; it must not be presented as the author's triangulation. The reconstruction audit is 2,138 welded vertices and 4,272 triangles.

Coordinates in the independent definition use the exact integer grid `coordinate = geometric coordinate × 10000`. The source pin recorded for the numerical extraction is `d90313a717994936f254990f88d2624bbcce5bcd`.

## Eight-child substitution

The child records below are exact records from the independent definition. `p` is the coordinate permutation, `s` is its sign vector, and `u` is the recorded integer translation. Together `(p,s)` encode a signed permutation matrix `R`; every row has determinant `+1`, so these are **proper rotations**, not reflections.

| child | `p` | `s` | `u` |
|---:|:---:|:---:|:---:|
| 0 | `[0,1,2]` | `[1,1,1]` | `[0,0,0]` |
| 1 | `[1,0,2]` | `[1,1,-1]` | `[0,0,4]` |
| 2 | `[0,2,1]` | `[1,-1,1]` | `[0,4,0]` |
| 3 | `[2,0,1]` | `[1,-1,-1]` | `[0,4,4]` |
| 4 | `[2,1,0]` | `[-1,1,1]` | `[4,0,0]` |
| 5 | `[1,2,0]` | `[-1,1,-1]` | `[4,0,4]` |
| 6 | `[0,1,2]` | `[-1,-1,1]` | `[4,4,0]` |
| 7 | `[0,1,2]` | `[1,1,1]` | `[1,1,1]` |

In the source placement convention, refinement is `refine(GH, 2t + Gu)`: apply the eight rows to a parent placement with proper rotation `G` and translation `t`, using each row's `R` and `u`. After `n` refinements the finite patch contains `8^n` child placements and has linear scale `2^n` (a finite nested patch, not an asserted infinite filling).

## Rendering behavior

- Levels 0–3 render each tile's full 192-feature geometry.
- Levels 4–5 render all tile placements at their correct positions using a 48-triangle carrier overview; this is a complete placement render, not sampling. The selected tile is rendered with its full 4,272-triangle mesh.
- Unselected outlines are omitted at high levels.
- Family colors are top-level substitution groups. Each of the 24 proper rotations has one unique hue; the Clay family is uniform. The interactive legend filters groups in the current mode, with hide/show controls and **Show all**; those filters persist in the URL.

## Validation and limits

The supplied validation checks exact integer-grid contacts through levels 0–3. Occupancy and placement-count checks extend through levels 4–5:

| level `n` | carrier copies | linear scale |
|---:|---:|---:|
| 0 | 1 | 1 |
| 1 | 8 | 2 |
| 2 | 64 | 4 |
| 3 | 512 | 8 |
| 4 | 4,096 | 16 |
| 5 | 32,768 | 32 |

At level 1, **48 internal panel pairs** and **384 physical feature matches** mated, with **zero errors**. Exact contact validation remains bounded to levels 0–3, with **43,008 checked pairs** at level 3; no full-feature contact check is claimed for levels 4–5. That level-1 contact-validation record also reports 3,024 coordinates checked, zero non-integer coordinates, zero internal-panel failures, zero physical-feature failures, and no other failures.

These are finite-patch and coordinate/contact results only. The undecorated seven-cube carrier is periodic under lattice translations; neither it nor a finite decorated patch proves an infinite aperiodic tiling or an infinite-space fill. The cited result is a **proposed preprint result**, not a peer-reviewed claim. Any height magnification, exploded copy view, or similar renderer mode is illustrative UI and must be labeled as such; it is not the exact geometry or an exact tiling.

## Sources

1. **Primary geometry reference:** [arXiv:2609.19214v1, §§2–3](https://arxiv.org/html/2609.19214v1). Use as a preprint/proposed-result source; do not upgrade its status to peer reviewed.
2. **Independent reference:** [arXiv:2609.24779v1](https://arxiv.org/html/2609.24779v1).
3. **Context:** [Quanta Magazine](https://www.quantamagazine.org/update/167384/).
4. **Inspiration only:** [Natty Over, X status](https://x.com/nattyover/status/2102764113684533336). This is not a geometry or licensing authority.
