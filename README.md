# Einstein Tile 3D Viz

Live demo: <https://sager611.github.io/einstein-tile-3d-viz/>  
Repository: <https://github.com/Sager611/einstein-tile-3d-viz>

A light-canvas React/Vite/TypeScript/Three.js/shadcn viewer for an independent reconstruction of the paper's exact **Chair44** geometry—not a generic voxel chair.

## Geometry

- 24 exposed panels and 192 panel features.
- Independent reconstruction audit: 4,272 triangles and 2,138 welded vertices.
- Proper eight-child substitution hierarchy: levels 0–6 contain 1/8/64/512/4,096/32,768/262,144 placements.
- Levels 0–3 use full 192-feature tiles. Levels 4–6 render all placements at their correct positions with a no-sampling 48-triangle carrier overview; selected tiles retain full 4,272-triangle geometry and unselected outlines are omitted.
- This is a finite patch. Exploded and magnified views are illustrative, not exact tilings. The cited work is a preprint/proposed result; this project makes no journal or peer-review claim.

## Controls

Adjust levels, spread, and layers; orbit, pan, and zoom; use presets; select/focus tiles; adjust one-tile height. The color legend hides/shows current-mode groups or **Show all**; its filters persist in shareable URL hashes. Optional UI affordances provide tooltips/Info and PNG export.

## Warp and Lean proof

The **Warp** drawer (wave button) deforms space by maps that commute with every motion used by Chair44 tilings (the 24 cube rotations with the body-centred cubic lattice, space group I432). Such a map turns every Chair44 tiling into a tiling by one new, congruent solid.

Three families, **A**, **B**, **C**, all proved in [`lean/`](lean/README.md) (`familyA/B/C`, `FamilyFinal.lean`). Each is `Φ_s = id + s·V` with `V(x) = Σ_R cos(2π k·Rx) R⁻¹e` over the 24 rotations: A `k = (1, ½, ½)`, `e = (1,1,0)`; B `k = (0, 2, 1)`, `e = (1,0,0)`; C `k = (3/2, 3/2, 1)`, `e = (1,0,0)`. For **every** amplitude `0 < s ≤ 10⁻⁹`, Lean 4 + Mathlib prove, assuming only the paper's Theorem 1.2: `Φ_s(Q)` tiles space, differs from Chair44, has no symmetry, and its tilings of this form have no translational period. The true displacement is below 10⁻⁷; the **Magnify** slider scales it up (up to about 2·10⁷×) for viewing. Lean also proves different `s` give non-congruent solids (`familyA/B/C_noncongruent`), so each family is infinite. Not proved: non-congruence across families.

Paper-ready figures of the three families: [docs/figures](docs/figures/README.md).

Different arm sizes are impossible in both frameworks: see [research/asymmetric-arms](research/asymmetric-arms/README.md) (Lean: every equivariant warp fixes all cube corners).

The [Lean proof workflow](.github/workflows/lean.yml) rebuilds `lean/` and audits that every theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Development

```sh
npm ci
npm run dev
npm test
npm run build
```

Correctness coverage includes exact integer-grid contact checks through level 3 (**43,008 checked pairs** at level 3), plus occupancy and placement-count checks through level 6. The numerical extraction records source pin `d90313a717994936f254990f88d2624bbcce5bcd`.

`qa/mobile.html` is a 390×844 development fixture for manual visual QA. It is not a physical-touch test suite.

See [geometry and provenance](docs/geometry.md) and [third-party/licensing notes](THIRD_PARTY.md) for source references, reconstruction limits, and licensing details.
