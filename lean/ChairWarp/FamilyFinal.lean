import ChairWarp.Family
import ChairWarp.Final

/-!
# Three infinite families of rigid, non-periodic warped Chair44 tiles

For a wave specification `w` with an integer *certificate* (a point `pt P8` on Chair44's surface that
the field pushes straight out of the solid), every amplitude `0 < s ≤ 10⁻⁹` gives a solid
`warp_{w,s} '' Q` that
1. tiles `ℝ³` (by the same placements as Chair44),
2. is rigid (no non-identity self-isometry),
3. has only non-periodic tilings of that form, and
4. differs from Chair44.

Families: `famA` (the original wave, `k = (1, ½, ½)`, `e = (1,1,0)`), `famB` (`k = (3/2, 1, ½)`,
`e = (1,0,0)`) and `famC` (`k = (3/2, 3/2, 1)`, `e = (1,0,0)`).
-/

open Set

namespace WaveSpec

noncomputable def pt (P8 : V) : E := WithLp.toLp 2 fun j => (P8 j : ℝ) / 8

/-- Integer data certifying that the field at `pt P8` is `(0, 0, a)` with `a < 0` and that `pt P8`
lies on Chair44's bottom face `z = 0`, away from every dent and bump. All fields are `decide`-able. -/
structure Cert (w : WaveSpec) (P8 : V) : Prop where
  even : ∀ R ∈ Rot.R24, 2 ∣ w.num16 P8 R
  sqrt2 : ∀ i, ∑ R ∈ Rot.S24, cosB (w.qR P8 R) * w.cR R i = 0
  f0 : ∑ R ∈ Rot.S24, cosA (w.qR P8 R) * w.cR R 0 = 0
  f1 : ∑ R ∈ Rot.S24, cosA (w.qR P8 R) * w.cR R 1 = 0
  f2 : ∑ R ∈ Rot.S24, cosA (w.qR P8 R) * w.cR R 2 < 0
  cell : ∀ i, 0 ≤ P8 i ∧ P8 i ≤ 8
  z0 : P8 2 = 0
  notDent : ∀ f ∈ feats, f.a < 0 → ∃ j, j ≠ f.ax ∧ 100 ≤ |1250 * P8 j - f.c j|
  outside : ∀ b ∈ boxes, 0 ≤ (b 2).1 ∨ 1250 * P8 0 < (b 0).1 ∨ (b 0).2 < 1250 * P8 0 ∨
    1250 * P8 1 < (b 1).1 ∨ (b 1).2 < 1250 * P8 1

lemma pt_apply (P8 : V) (j : Fin 3) : pt P8 j = (P8 j : ℝ) / 8 := rfl

lemma pt_mem {w : WaveSpec} {P8 : V} (hc : w.Cert P8) : pt P8 ∈ Q := by
  left
  refine ⟨⟨![0, 0, 0], by simp [cells], fun i => ?_⟩, fun f hf ha hd => ?_⟩
  · rw [pt_apply]
    obtain ⟨h0, h8⟩ := hc.cell i
    have a : (0 : ℝ) ≤ P8 i := by exact_mod_cast h0
    have b : (P8 i : ℝ) ≤ 8 := by exact_mod_cast h8
    have z : (((![0, 0, 0] : V) i : ℤ) : ℝ) = 0 := by fin_cases i <;> simp
    rw [z]; constructor <;> linarith
  · obtain ⟨j, hj, hsep⟩ := hc.notDent f hf ha
    have hu := (hd.2 j hj).1
    simp only [uu, sc, η, pt_apply] at hu
    rw [abs_lt] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hs : (100 : ℝ) ≤ |((1250 * P8 j - f.c j : ℤ) : ℝ)| := by exact_mod_cast hsep
    push_cast at hs
    rcases le_abs'.mp hs with h | h <;> linarith

variable {w : WaveSpec} (hw : w.Good) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10 ^ 9)

lemma warp_pt {P8 : V} (hc : w.Cert P8) (i : Fin 3) :
    w.warp hw s hs0 hs (pt P8) i =
      pt P8 i + s * ((∑ R ∈ Rot.S24, cosA (w.qR P8 R) * w.cR R i : ℤ) : ℝ) := by
  rw [warp_apply, warpFun, PiLp.add_apply]
  unfold pt
  rw [w.field_eighth s P8 hc.even hc.sqrt2 i]

/-- A self-isometry of the warped tile is a near-symmetry of Chair44 with defect `96 s`. -/
lemma nearSym {τ : E ≃ᵢ E} (h : τ '' (w.warp hw s hs0 hs '' Q) = w.warp hw s hs0 hs '' Q) :
    NearSym (96 * s) τ := by
  set W := w.warp hw s hs0 hs
  intro q hq
  have hmem : τ (W q) ∈ W '' Q := h ▸ mem_image_of_mem τ (mem_image_of_mem W hq)
  obtain ⟨q', hq', hq'e⟩ := hmem
  refine ⟨q', hq', ?_⟩
  have h1 : ‖τ q - τ (W q)‖ ≤ 48 * s := by
    rw [← dist_eq_norm, τ.dist_eq, dist_eq_norm, norm_sub_rev]
    exact w.norm_warp_sub_le hw s hs0 hs q
  have h2 : ‖W q' - q'‖ ≤ 48 * s := w.norm_warp_sub_le hw s hs0 hs q'
  calc ‖τ q - q'‖ = ‖(τ q - τ (W q)) + (W q' - q')‖ := by rw [hq'e]; congr 1; abel
    _ ≤ ‖τ q - τ (W q)‖ + ‖W q' - q'‖ := norm_add_le _ _
    _ ≤ 96 * s := by linarith

/-- **Rigidity** for every member of every family. -/
theorem rigid : ∀ σ : E ≃ᵢ E, σ '' (w.warp hw s hs0 hs '' Q) = w.warp hw s hs0 hs '' Q → σ = 1 := by
  intro σ hσ
  have hd0 : (0 : ℝ) ≤ 96 * s := by positivity
  have hd7 : 96 * s ≤ 1 / 10 ^ 7 := by
    have := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 96); linarith [this,
      show (96 : ℝ) * (1 / 10 ^ 9) ≤ 1 / 10 ^ 7 by norm_num]
  refine isometry_eq_one_of_near σ (vec ![1, 1, 1]) (C := 300 * (96 * s)) (by positivity)
    (by linarith) fun n x hx => ?_
  refine near_id_on_box hd0 hd7 (nearSym hw hs0 hs (pow_image_eq hσ n)) x fun i => ?_
  have := (abs_apply_le (x - vec ![1, 1, 1]) i).trans hx
  simp only [PiLp.sub_apply, vec_apply] at this
  have h1 : ((![1, 1, 1] : V) i : ℝ) = 1 := by fin_cases i <;> simp
  rw [h1, abs_le] at this
  constructor <;> linarith [this.1, this.2]

/-- For `s > 0` the warp pushes `pt P8` out of Chair44, so the solid is new. -/
theorem image_ne {P8 : V} (hc : w.Cert P8) (hpos : 0 < s) : w.warp hw s hs0 hs '' Q ≠ Q := by
  intro h
  have hmem : w.warp hw s hs0 hs (pt P8) ∈ Q := h ▸ mem_image_of_mem _ (pt_mem hc)
  obtain ⟨b, hb, hin⟩ := Q_sub hmem
  have c0 := warp_pt hw hs0 hs hc 0
  have c1 := warp_pt hw hs0 hs hc 1
  have c2 := warp_pt hw hs0 hs hc 2
  rw [hc.f0] at c0; rw [hc.f1] at c1
  simp only [Int.cast_zero, mul_zero, add_zero, pt_apply] at c0 c1
  rw [pt_apply, hc.z0] at c2
  have hneg : ((∑ R ∈ Rot.S24, cosA (w.qR P8 R) * w.cR R 2 : ℤ) : ℝ) ≤ -1 := by
    have := hc.f2; exact_mod_cast (show _ ≤ (-1 : ℤ) by omega)
  obtain ⟨l0, u0⟩ := hin 0; obtain ⟨l1, u1⟩ := hin 1; obtain ⟨l2, u2⟩ := hin 2
  rw [c0] at l0 u0; rw [c1] at l1 u1; rw [c2] at l2 u2
  simp only [Int.cast_zero, zero_div, zero_add] at l2
  rcases hc.outside b hb with h | h | h | h | h
  · have : (0 : ℝ) ≤ (b 2).1 := by exact_mod_cast h
    nlinarith
  · have : ((1250 * P8 0 : ℤ) : ℝ) + 1 ≤ (b 0).1 := by exact_mod_cast h
    push_cast at this; linarith
  · have : ((b 0).2 : ℝ) + 1 ≤ ((1250 * P8 0 : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  · have : ((1250 * P8 1 : ℤ) : ℝ) + 1 ≤ (b 1).1 := by exact_mod_cast h
    push_cast at this; linarith
  · have : ((b 1).2 : ℝ) + 1 ≤ ((1250 * P8 1 : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith

variable {ι : Type*}

/-- **Family theorem.** For every certified wave `w` and every amplitude `0 < s ≤ 10⁻⁹`, warping any
registered, non-periodic Chair44 tiling gives a tiling by a rigid solid, different from Chair44, with
no nonzero translational period. -/
theorem family_concrete {P8 : V} (hc : w.Cert P8) (hpos : 0 < s) (g : ι → (E ≃ᵢ E)) [Nonempty ι]
    (hT : Tiling Q g) (hg : ∀ i, g i ∈ GammaGeom)
    (hper : ∀ v : E, IsSymmetry Q g (transl v) → v = 0) :
    Tiling (w.warp hw s hs0 hs '' Q) g ∧
    (∀ σ : E ≃ᵢ E, σ '' (w.warp hw s hs0 hs '' Q) = w.warp hw s hs0 hs '' Q → σ = 1) ∧
    (∀ v : E, IsSymmetry (w.warp hw s hs0 hs '' Q) g (transl v) → v = 0) ∧
    w.warp hw s hs0 hs '' Q ≠ Q := by
  have hcomm := w.warp_comm hw s hs0 hs
  refine ⟨hT.warp GammaGeom _ hcomm hg, rigid hw hs0 hs, fun v hsym => ?_, image_ne hw hs0 hs hc hpos⟩
  exact hper v (Tiling.warp_symm GammaGeom _ hcomm hg (rigid hw hs0 hs) hsym).2

end WaveSpec

/-! ## The three families -/

def famA : WaveSpec := ⟨![2, 1, 1], ![1, 1, 0]⟩
def famB : WaveSpec := ⟨![3, 2, 1], ![1, 0, 0]⟩
def famC : WaveSpec := ⟨![3, 3, 2], ![1, 0, 0]⟩

lemma famA_good : famA.Good := by decide +kernel
lemma famB_good : famB.Good := by decide +kernel
lemma famC_good : famC.Good := by decide +kernel

lemma famA_cert : famA.Cert ![6, 4, 0] :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
lemma famB_cert : famB.Cert ![2, 4, 0] :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
lemma famC_cert : famC.Cert ![2, 4, 0] :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

section
variable {ι : Type*} (g : ι → (E ≃ᵢ E)) [Nonempty ι] (hT : Tiling Q g) (hg : ∀ i, g i ∈ GammaGeom)
  (hper : ∀ v : E, IsSymmetry Q g (transl v) → v = 0) {s : ℝ} (hpos : 0 < s) (hs : s ≤ 1 / 10 ^ 9)
include hT hg hper

/-- **Family A**: every amplitude `0 < s ≤ 10⁻⁹` gives a new rigid, non-periodic tile. -/
theorem familyA :
    Tiling (famA.warp famA_good s hpos.le hs '' Q) g ∧
    (∀ σ : E ≃ᵢ E, σ '' (famA.warp famA_good s hpos.le hs '' Q) = famA.warp famA_good s hpos.le hs '' Q → σ = 1) ∧
    (∀ v : E, IsSymmetry (famA.warp famA_good s hpos.le hs '' Q) g (transl v) → v = 0) ∧
    famA.warp famA_good s hpos.le hs '' Q ≠ Q :=
  WaveSpec.family_concrete famA_good hpos.le hs famA_cert hpos g hT hg hper

/-- **Family B**: every amplitude `0 < s ≤ 10⁻⁹` gives a new rigid, non-periodic tile. -/
theorem familyB :
    Tiling (famB.warp famB_good s hpos.le hs '' Q) g ∧
    (∀ σ : E ≃ᵢ E, σ '' (famB.warp famB_good s hpos.le hs '' Q) = famB.warp famB_good s hpos.le hs '' Q → σ = 1) ∧
    (∀ v : E, IsSymmetry (famB.warp famB_good s hpos.le hs '' Q) g (transl v) → v = 0) ∧
    famB.warp famB_good s hpos.le hs '' Q ≠ Q :=
  WaveSpec.family_concrete famB_good hpos.le hs famB_cert hpos g hT hg hper

/-- **Family C**: every amplitude `0 < s ≤ 10⁻⁹` gives a new rigid, non-periodic tile. -/
theorem familyC :
    Tiling (famC.warp famC_good s hpos.le hs '' Q) g ∧
    (∀ σ : E ≃ᵢ E, σ '' (famC.warp famC_good s hpos.le hs '' Q) = famC.warp famC_good s hpos.le hs '' Q → σ = 1) ∧
    (∀ v : E, IsSymmetry (famC.warp famC_good s hpos.le hs '' Q) g (transl v) → v = 0) ∧
    famC.warp famC_good s hpos.le hs '' Q ≠ Q :=
  WaveSpec.family_concrete famC_good hpos.le hs famC_cert hpos g hT hg hper

end
