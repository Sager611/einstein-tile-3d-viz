# Can Chair44's arms have different sizes?

Question: is there an aperiodic 3D monotile derived from Chair44 whose chair arms have unequal
lengths or thicknesses, so the infinite pattern looks different?

**Answer: not within either framework that produced Chair44 and its warps.** Both obstructions are
machine-checked (Python below; the second also in Lean).

## 1. Substitution route (new decorated carriers)

1. Arms of unequal proportions cannot be rotated into another axis, so tilings may use only the 8
   axis-preserving frames (sign flips, including mirrors).
2. `a1.py`, `a2b.py`: carriers `A×B×C` box minus a corner, `A,B,C ≤ 4`, every thickness, inflations
   `diag(k1,k2,k3)` with at most 36 copies (4,476 pairs). The only carriers with a self-similar
   cutting using those frames are the chair and its axis-wise stretches, always at uniform
   inflation 2. No anisotropic inflation works.
3. `a3.py`: thick/thin symmetric arms (`3×3×3` and `4×4×4` boxes minus corners) with all 24
   rotations have no cutting at inflation 2 or 3.
4. `a3.py`, `a4.py`: the stretched-chair substitution is unique and needs mirror-image children;
   27 unit faces per supertile join a tile to its exact mirror image.
   *Lemma (paper proof):* if `B` is the mirror image of `A` across a shared face and near it
   `A = {z ≤ f(u)}`, then `B = {z ≥ −f(u)}`; disjoint interiors force `f ≤ 0`, covering forces
   `f ≥ 0`, so the face must be flat. Over the whole contact closure this forces **21 of 24 panel
   roles flat**.
5. `a5.py`: decorating the 3 remaining panels constrains no contact at all (empty legal-contact
   atlas), so no Chair44-style certificate (contact atlas + halving identity) can exist.

## 2. Warp route (equivariant deformations of Chair44)

Chair44 tilings place tiles by the motion group `Γ` (24 cube rotations × body-centred lattice).
Lean theorem `equivariant_fixes_grid` (`lean/ChairWarp/Obstruction.lean`): **every map commuting with
`Γ` fixes every integer grid point**. The half-turns `diag(1,−1,−1)` and `diag(−1,1,−1)`, each
followed by an even translation, fix any grid point `v`, and their only common fixed vector is 0.
So equivariant warps can bend faces and edges (as the explorer's Warp drawer shows) but can never
move a cube corner, and so cannot resize an arm.

## Literature

No established aperiodic tile from an unequal-arm L or chair is known (search notes in the session;
Goodman-Strauss 1998 gives matching rules for substitution tilings under hypotheses, but does not
cover bare anisotropic chairs; arXiv:2609.23783 decorates the equal-arm 3D chair).

## Reproduce

```sh
cd research/asymmetric-arms
python3 a1.py   # chair with sign-flip frames: inflations
python3 a2b.py  # full carrier × inflation sweep (multiprocessing, minutes)
python3 a3.py   # mirror contacts; thick/thin arms with 24 rotations
python3 a5.py   # flat-panel count and empty atlas
```
