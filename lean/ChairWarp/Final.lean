import ChairWarp.Main
import ChairWarp.Pin
import ChairWarp.Ergodic

/-!
# The warped Chair44 is rigid, and its warped tilings are non-periodic

Every self-isometry `σ` of `warp '' Q` (and each of its powers) is a near-symmetry of Chair44 with
defect `d = 72 ε`, hence within `300 d` of the identity on the box (`near_id_on_box`); the mean
ergodic argument (`isometry_eq_one_of_near`) then forces `σ = 1`.
-/

open Set

lemma pow_image_eq {σ : E ≃ᵢ E} {S : Set E} (h : σ '' S = S) : ∀ n : ℕ, ⇑(σ ^ n) '' S = S := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', IsometryEquiv.coe_mul, image_comp, ih, h]

/-- A self-isometry of the warped tile is a near-symmetry of Chair44 with defect `72 ε`. -/
lemma nearSym_of_image {τ : E ≃ᵢ E} (h : τ '' (warp '' Q) = warp '' Q) :
    NearSym (72 * eps) τ := by
  intro q hq
  have hmem : τ (warp q) ∈ warp '' Q := h ▸ mem_image_of_mem τ (mem_image_of_mem warp hq)
  obtain ⟨q', hq', hq'e⟩ := hmem
  refine ⟨q', hq', ?_⟩
  have h1 : ‖τ q - τ (warp q)‖ ≤ 36 * eps := by
    rw [← dist_eq_norm, τ.dist_eq, dist_eq_norm, norm_sub_rev]; exact norm_warp_sub_le q
  have h2 : ‖warp q' - q'‖ ≤ 36 * eps := norm_warp_sub_le q'
  calc ‖τ q - q'‖ = ‖(τ q - τ (warp q)) + (warp q' - q')‖ := by rw [hq'e]; congr 1; abel
    _ ≤ ‖τ q - τ (warp q)‖ + ‖warp q' - q'‖ := norm_add_le _ _
    _ ≤ 72 * eps := by linarith

/-- **Rigidity.** The warped Chair44 has no non-identity self-isometry. -/
theorem warp_rigid : ∀ σ : E ≃ᵢ E, σ '' (warp '' Q) = warp '' Q → σ = 1 := by
  intro σ hσ
  have hε : (0 : ℝ) ≤ 72 * eps := by simp [eps]
  have hε7 : 72 * eps ≤ 1 / 10 ^ 7 := by simp [eps]; norm_num
  refine isometry_eq_one_of_near σ (vec ![1, 1, 1]) (C := 300 * (72 * eps)) (by positivity)
    (by simp [eps]; norm_num) fun n x hx => ?_
  refine near_id_on_box hε hε7 (nearSym_of_image (pow_image_eq hσ n)) x fun i => ?_
  have := (abs_apply_le (x - vec ![1, 1, 1]) i).trans hx
  simp only [PiLp.sub_apply, vec_apply] at this
  have h1 : ((![1, 1, 1] : V) i : ℝ) = 1 := by fin_cases i <;> simp
  rw [h1, abs_le] at this
  constructor <;> linarith [this.1, this.2]

/-! ## The warped tile is a genuinely different solid -/

lemma x0_not_dent : ∀ f ∈ feats, f.a < 0 → ∃ j, j ≠ f.ax ∧ 100 ≤ |(![7500, 5000, 0] : V) j - f.c j| := by
  decide +kernel

lemma warp_x0_boxes : ∀ b ∈ boxes, 0 ≤ (b 2).1 ∨ 7500 < (b 0).1 ∨ (b 0).2 < 7500 ∨
    5000 < (b 1).1 ∨ (b 1).2 < 5000 := by
  decide +kernel

lemma x0_mem : x0 ∈ Q := by
  left
  refine ⟨⟨![0, 0, 0], by simp [cells], fun i => ?_⟩, fun f hf ha hd => ?_⟩
  · rw [x0_apply]; fin_cases i <;> simp [P8] <;> norm_num
  · obtain ⟨j, hj, hsep⟩ := x0_not_dent f hf ha
    have hu := (hd.2 j hj).1
    simp only [uu, sc, η, x0_apply] at hu
    rw [abs_lt] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hP : (((![7500, 5000, 0] : V) j : ℤ) : ℝ) = 1250 * (P8 j : ℝ) := by
      fin_cases j <;> simp [P8] <;> norm_num
    have hs : (100 : ℝ) ≤ |(((![7500, 5000, 0] : V) j : ℤ) : ℝ) - (f.c j : ℝ)| := by
      exact_mod_cast hsep
    rw [hP] at hs
    rcases le_abs'.mp hs with h | h <;> linarith

/-- The warp pushes a point of Chair44's bottom face out of the solid, so `warp '' Q ≠ Q`. -/
theorem warp_image_ne : warp '' Q ≠ Q := by
  intro h
  have hmem : warp x0 ∈ Q := h ▸ mem_image_of_mem warp x0_mem
  obtain ⟨b, hb, hin⟩ := Q_sub hmem
  have c0 : warp x0 0 = 3 / 4 := by rw [warp_x0]; simp [x0]
  have c1 : warp x0 1 = 1 / 2 := by rw [warp_x0]; simp [x0]
  have c2 : warp x0 2 = -4 * eps := by rw [warp_x0]; simp [x0]; ring
  have he : (0 : ℝ) < eps := by simp [eps]
  obtain ⟨l0, u0⟩ := hin 0; obtain ⟨l1, u1⟩ := hin 1; obtain ⟨l2, u2⟩ := hin 2
  rw [c0] at l0 u0; rw [c1] at l1 u1; rw [c2] at l2 u2
  rcases warp_x0_boxes b hb with h | h | h | h | h
  · have : (0 : ℝ) ≤ (b 2).1 := by exact_mod_cast h
    nlinarith
  · have : (7500 : ℝ) + 1 ≤ (b 0).1 := by exact_mod_cast h
    linarith
  · have : ((b 0).2 : ℝ) + 1 ≤ 7500 := by exact_mod_cast h
    linarith
  · have : (5000 : ℝ) + 1 ≤ (b 1).1 := by exact_mod_cast h
    linarith
  · have : ((b 1).2 : ℝ) + 1 ≤ 5000 := by exact_mod_cast h
    linarith

variable {ι : Type*}

/-- **Main theorem, concrete form.** Let `T = (g i '' Q)` be any tiling of `ℝ³` by Chair44 whose
placements lie in its motion group and which has no nonzero translational symmetry (both supplied
by the paper's Theorem 1.2). Then the explicit, non-trivial, `Γ`-equivariant homeomorphism `warp`
turns it into a tiling by congruent copies of the single rigid solid `warp '' Q` with no nonzero
translational symmetry, and the new solid genuinely differs from Chair44. -/
theorem chair44_warp_concrete (g : ι → (E ≃ᵢ E)) [Nonempty ι]
    (hT : Tiling Q g) (hg : ∀ i, g i ∈ GammaGeom)
    (hper : ∀ v : E, IsSymmetry Q g (transl v) → v = 0) :
    Tiling (warp '' Q) g ∧
    (∀ σ : E ≃ᵢ E, σ '' (warp '' Q) = warp '' Q → σ = 1) ∧
    (∀ v : E, IsSymmetry (warp '' Q) g (transl v) → v = 0) ∧
    warp '' Q ≠ Q := by
  obtain ⟨hTile, _, hrig, _⟩ := chair44_warp_main Q g hT hg hper
  exact ⟨hTile, warp_rigid, hrig warp_rigid, warp_image_ne⟩
