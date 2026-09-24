import ChairWarp.Warp

/-!
# Parameterized families of equivariant warps

A wave specification `w` gives integer vectors `k2 = 2k` and `e`. For every amplitude `s` the field

  `fieldW w s x = s • ∑_{R ∈ R24} cos (2π k·(R x)) • R⁻¹ e`

is periodic under the body-centred lattice (when `k2 0 + k2 1 + k2 2` is even) and
rotation-equivariant, so `warpW w s = id + fieldW w s` commutes with every motion of `GammaGeom`.
For `0 ≤ s ≤ 10⁻⁹` (and small integer data) it is a homeomorphism moving points by at most `48 s`.
-/

open Real
open scoped BigOperators

structure WaveSpec where
  k2 : V
  e : V

namespace WaveSpec

/-- Decidable side conditions: lattice periodicity and small coefficients. -/
def Good (w : WaveSpec) : Prop :=
  2 ∣ w.k2 0 + w.k2 1 + w.k2 2 ∧ |w.k2 0| + |w.k2 1| + |w.k2 2| ≤ 8 ∧ |w.e 0| + |w.e 1| + |w.e 2| ≤ 2

instance (w : WaveSpec) : Decidable w.Good := by unfold Good; infer_instance

noncomputable def kdot (w : WaveSpec) (y : E) : ℝ :=
  ((w.k2 0 : ℝ) * y 0 + (w.k2 1 : ℝ) * y 1 + (w.k2 2 : ℝ) * y 2) / 2

noncomputable def wave (w : WaveSpec) (y : E) : ℝ := Real.cos (2 * π * w.kdot y)

noncomputable def field (w : WaveSpec) (s : ℝ) (x : E) : E :=
  s • ∑ R ∈ Rot.S24, w.wave (R.lin x) • R.inv.lin (vec w.e)

noncomputable def warpFun (w : WaveSpec) (s : ℝ) (x : E) : E := x + w.field s x

lemma kdot_add (w : WaveSpec) (y z : E) : w.kdot (y + z) = w.kdot y + w.kdot z := by
  simp [kdot]; ring

lemma kdot_sub (w : WaveSpec) (y z : E) : w.kdot y - w.kdot z = w.kdot (y - z) := by
  simp [kdot]; ring

lemma wave_add_bcc (w : WaveSpec) (hw : w.Good) (y : E) {c : V} (hc : bcc c) :
    w.wave (y + vec c) = w.wave y := by
  obtain ⟨a, ha⟩ := hc.1
  obtain ⟨b, hb⟩ := hc.2
  obtain ⟨g, hg⟩ := hw.1
  -- `k2 · c = c 1 (k2 0 + k2 1 + k2 2) + 2 (k2 0 a - k2 2 b)` is even
  have hint : w.k2 0 * c 0 + w.k2 1 * c 1 + w.k2 2 * c 2 =
      2 * (c 1 * g + w.k2 0 * a - w.k2 2 * b) := by
    have e0 : c 0 = c 1 + 2 * a := by omega
    have e2 : c 2 = c 1 - 2 * b := by omega
    rw [e0, e2]; linear_combination c 1 * hg
  have hk : w.kdot (vec c) = ((c 1 * g + w.k2 0 * a - w.k2 2 * b : ℤ) : ℝ) := by
    simp only [kdot, vec_apply]
    have : ((w.k2 0 * c 0 + w.k2 1 * c 1 + w.k2 2 * c 2 : ℤ) : ℝ) =
        ((2 * (c 1 * g + w.k2 0 * a - w.k2 2 * b) : ℤ) : ℝ) := by rw [hint]
    push_cast at this ⊢; linarith
  rw [wave, wave, kdot_add, hk, mul_add]
  have : 2 * π * ((c 1 * g + w.k2 0 * a - w.k2 2 * b : ℤ) : ℝ) =
      ((c 1 * g + w.k2 0 * a - w.k2 2 * b : ℤ) : ℝ) * (2 * π) := by ring
  rw [this, Real.cos_add_int_mul_two_pi]

lemma field_add_bcc (w : WaveSpec) (hw : w.Good) (s : ℝ) (x : E) {t : V} (ht : bcc t) :
    w.field s (x + vec t) = w.field s x := by
  unfold field
  congr 1
  refine Finset.sum_congr rfl fun R hR => ?_
  rw [map_add, Rot.lin_vec, w.wave_add_bcc hw _ (bcc_act (Rot.mem_S24.mp hR) ht)]

lemma field_rot (w : WaveSpec) (s : ℝ) {S : Rot} (hS : S ∈ Rot.R24) (x : E) :
    w.field s (S.lin x) = S.lin (w.field s x) := by
  unfold field
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_nbij' (fun R => R.comp S) (fun Q => Q.comp S.inv) ?_ ?_ ?_ ?_ ?_
  · intro R hR
    exact Rot.mem_S24.mpr (Rot.comp_mem _ (Rot.mem_S24.mp hR) _ hS)
  · intro Q hQ
    exact Rot.mem_S24.mpr (Rot.comp_mem _ (Rot.mem_S24.mp hQ) _ (Rot.inv_spec S hS).1)
  · intro R hR
    exact Rot.comp_inv_cancel_right R (Rot.mem_S24.mp hR) S hS
  · intro Q hQ
    have h1 := Rot.comp_inv_cancel_right Q (Rot.mem_S24.mp hQ) S.inv (Rot.inv_spec S hS).1
    show (Q.comp S.inv).comp S = Q
    rw [Rot.inv_inv_eq S hS] at h1; exact h1
  · intro R hR
    rw [map_smul, ← Rot.lin_comp, ← Rot.lin_comp, Rot.comp_inv_comp R (Rot.mem_S24.mp hR) S hS]

lemma warpFun_pose (w : WaveSpec) (hw : w.Good) (s : ℝ) (P : Pose) (hP : P.InGamma) (x : E) :
    w.warpFun s (P.toFun x) = P.toFun (w.warpFun s x) := by
  simp only [warpFun, Pose.toFun]
  rw [w.field_add_bcc hw _ _ hP.2, w.field_rot s hP.1, map_add]
  abel

/-! ## Size and Lipschitz bounds -/

lemma norm_le_abs_sum (x : E) : ‖x‖ ≤ |x 0| + |x 1| + |x 2| := by
  have h : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have hn := norm_nonneg x
  nlinarith [sq_abs (x 0), sq_abs (x 1), sq_abs (x 2), abs_nonneg (x 0), abs_nonneg (x 1),
    abs_nonneg (x 2), mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1)),
    mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 2)), mul_nonneg (abs_nonneg (x 1)) (abs_nonneg (x 2))]

lemma norm_e_le (w : WaveSpec) (hw : w.Good) : ‖(vec w.e : E)‖ ≤ 2 := by
  refine (norm_le_abs_sum _).trans ?_
  simp only [vec_apply]
  have := hw.2.2
  have h : ((|w.e 0| + |w.e 1| + |w.e 2| : ℤ) : ℝ) ≤ 2 := by exact_mod_cast this
  push_cast at h; exact h

lemma abs_kdot_le (w : WaveSpec) (hw : w.Good) (z : E) : |w.kdot z| ≤ 4 * ‖z‖ := by
  have h0 := PiLp.norm_apply_le z 0
  have h1 := PiLp.norm_apply_le z 1
  have h2 := PiLp.norm_apply_le z 2
  simp only [Real.norm_eq_abs] at h0 h1 h2
  have hk : ((|w.k2 0| + |w.k2 1| + |w.k2 2| : ℤ) : ℝ) ≤ 8 := by exact_mod_cast hw.2.1
  push_cast at hk
  unfold kdot
  rw [abs_div, abs_two]
  have t0 : |(w.k2 0 : ℝ) * z 0| ≤ |(w.k2 0 : ℝ)| * ‖z‖ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h0 (abs_nonneg _)
  have t1 : |(w.k2 1 : ℝ) * z 1| ≤ |(w.k2 1 : ℝ)| * ‖z‖ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have t2 : |(w.k2 2 : ℝ) * z 2| ≤ |(w.k2 2 : ℝ)| * ‖z‖ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have tri := abs_add_three ((w.k2 0 : ℝ) * z 0) ((w.k2 1 : ℝ) * z 1) ((w.k2 2 : ℝ) * z 2)
  have hn := norm_nonneg z
  have : |(w.k2 0 : ℝ) * z 0 + (w.k2 1 : ℝ) * z 1 + (w.k2 2 : ℝ) * z 2| ≤ 8 * ‖z‖ := by nlinarith
  linarith

lemma norm_term_sub (w : WaveSpec) (hw : w.Good) {R : Rot} (hR : R ∈ Rot.R24) (x y : E) :
    ‖w.wave (R.lin x) • R.inv.lin (vec w.e) - w.wave (R.lin y) • R.inv.lin (vec w.e)‖ ≤
      16 * π * ‖x - y‖ := by
  rw [← sub_smul, norm_smul, Rot.norm_lin (Rot.inv_spec R hR).1, Real.norm_eq_abs]
  have hwv : |w.wave (R.lin x) - w.wave (R.lin y)| ≤ 8 * π * ‖x - y‖ :=
    calc |w.wave (R.lin x) - w.wave (R.lin y)|
        ≤ |2 * π * w.kdot (R.lin x) - 2 * π * w.kdot (R.lin y)| := Real.abs_cos_sub_cos_le _ _
      _ = 2 * π * |w.kdot (R.lin (x - y))| := by
          rw [← mul_sub, w.kdot_sub, ← map_sub, abs_mul, abs_of_pos (by positivity)]
      _ ≤ 2 * π * (4 * ‖R.lin (x - y)‖) := by gcongr; exact w.abs_kdot_le hw _
      _ = 8 * π * ‖x - y‖ := by rw [Rot.norm_lin hR]; ring
  have he := w.norm_e_le hw
  calc |w.wave (R.lin x) - w.wave (R.lin y)| * ‖(vec w.e : E)‖ ≤ (8 * π * ‖x - y‖) * 2 :=
        mul_le_mul hwv he (norm_nonneg _) (by positivity)
    _ = 16 * π * ‖x - y‖ := by ring

theorem field_lipschitz (w : WaveSpec) (hw : w.Good) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10 ^ 9)
    (x y : E) : ‖w.field s x - w.field s y‖ ≤ (1 / 5) * ‖x - y‖ := by
  unfold field
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  have hsum : ‖∑ R ∈ Rot.S24, (w.wave (R.lin x) • R.inv.lin (vec w.e) -
      w.wave (R.lin y) • R.inv.lin (vec w.e))‖ ≤ 24 * (16 * π * ‖x - y‖) := by
    calc _ ≤ ∑ R ∈ Rot.S24, ‖w.wave (R.lin x) • R.inv.lin (vec w.e) -
          w.wave (R.lin y) • R.inv.lin (vec w.e)‖ := norm_sum_le _ _
      _ ≤ Rot.S24.card • (16 * π * ‖x - y‖) :=
          Finset.sum_le_card_nsmul _ _ _ fun R hR => w.norm_term_sub hw (Rot.mem_S24.mp hR) x y
      _ = 24 * (16 * π * ‖x - y‖) := by rw [Rot.S24_card]; simp
  have hπ := Real.pi_le_four
  have hn := norm_nonneg (x - y)
  have hsπ : s * (24 * (16 * π)) ≤ 1 / 5 := by
    have : s * (24 * (16 * π)) ≤ (1 / 10 ^ 9) * (24 * (16 * 4)) := by
      apply mul_le_mul hs (by linarith) (by positivity) (by norm_num)
    linarith [show (1 / 10 ^ 9 : ℝ) * (24 * (16 * 4)) ≤ 1 / 5 by norm_num]
  calc s * ‖_‖ ≤ s * (24 * (16 * π * ‖x - y‖)) := by gcongr
    _ = (s * (24 * (16 * π))) * ‖x - y‖ := by ring
    _ ≤ 1 / 5 * ‖x - y‖ := mul_le_mul_of_nonneg_right hsπ hn

theorem norm_field_le (w : WaveSpec) (hw : w.Good) {s : ℝ} (hs0 : 0 ≤ s) (x : E) :
    ‖w.field s x‖ ≤ 48 * s := by
  unfold field
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  have hsum : ‖∑ R ∈ Rot.S24, w.wave (R.lin x) • R.inv.lin (vec w.e)‖ ≤ 48 := by
    calc _ ≤ ∑ R ∈ Rot.S24, ‖w.wave (R.lin x) • R.inv.lin (vec w.e)‖ := norm_sum_le _ _
      _ ≤ Rot.S24.card • (2 : ℝ) := by
          refine Finset.sum_le_card_nsmul _ _ _ fun R hR => ?_
          rw [norm_smul, Rot.norm_lin (Rot.inv_spec R (Rot.mem_S24.mp hR)).1, Real.norm_eq_abs]
          calc |w.wave (R.lin x)| * ‖(vec w.e : E)‖ ≤ 1 * 2 :=
                mul_le_mul (Real.abs_cos_le_one _) (w.norm_e_le hw) (norm_nonneg _) zero_le_one
            _ = 2 := one_mul _
      _ = 48 := by rw [Rot.S24_card]; norm_num
  nlinarith

open scoped NNReal in
theorem warpFun_approx (w : WaveSpec) (hw : w.Good) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10 ^ 9) :
    ApproximatesLinearOn (w.warpFun s)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) Set.univ (1 / 5 : ℝ≥0) := by
  intro x _ y _
  have : w.warpFun s x - w.warpFun s y - (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) (x - y) =
      w.field s x - w.field s y := by
    simp [warpFun]; abel
  rw [this]
  simpa using w.field_lipschitz hw hs0 hs x y

/-- The warp `id + s · V_w` as a homeomorphism of `E`. -/
noncomputable def warp (w : WaveSpec) (hw : w.Good) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10 ^ 9) :
    E ≃ₜ E :=
  (w.warpFun_approx hw hs0 hs).toHomeomorph (w.warpFun s) (Or.inr (by
    simp [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.nnnorm_id]
    norm_num))

section
variable (w : WaveSpec) (hw : w.Good) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10 ^ 9)

lemma warp_apply (x : E) : w.warp hw s hs0 hs x = w.warpFun s x := rfl

theorem warp_comm : ∀ γ ∈ GammaGeom, ∀ x, w.warp hw s hs0 hs (γ x) = γ (w.warp hw s hs0 hs x) := by
  intro γ hγ
  induction hγ using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨P, hP, rfl⟩ := hg
    intro x
    simp [warp_apply, w.warpFun_pose hw s P hP]
  | one => intro x; rfl
  | mul a b _ _ ha hb =>
    intro x
    simp only [IsometryEquiv.mul_apply]
    rw [ha, hb]
  | inv a _ ha =>
    intro x
    have := ha (a⁻¹ x)
    simp only [IsometryEquiv.apply_inv_self] at this
    rw [this, IsometryEquiv.inv_apply_self]

theorem norm_warp_sub_le (x : E) : ‖w.warp hw s hs0 hs x - x‖ ≤ 48 * s := by
  rw [warp_apply, warpFun, add_sub_cancel_left]
  exact w.norm_field_le hw hs0 x

end

/-! ## Exact values at points with phases in eighth-turns -/

/-- `8 · (R x0)` for `8 · x0 = P8`. -/
def y8 (P8 : V) (R : Rot) (j : Fin 3) : ℤ := R.s j * P8 (R.p j)

/-- `16 · k · (R x0)`; when even, `k · (R x0) = qR / 8` with `qR = this / 2`. -/
def num16 (w : WaveSpec) (P8 : V) (R : Rot) : ℤ :=
  w.k2 0 * y8 P8 R 0 + w.k2 1 * y8 P8 R 1 + w.k2 2 * y8 P8 R 2

def qR (w : WaveSpec) (P8 : V) (R : Rot) : ℤ := w.num16 P8 R / 2

def cR (w : WaveSpec) (R : Rot) (i : Fin 3) : ℤ := R.inv.s i * w.e (R.inv.p i)

lemma kdot_eighth (w : WaveSpec) (P8 : V) {R : Rot} (heven : 2 ∣ w.num16 P8 R) :
    w.kdot (R.lin (WithLp.toLp 2 fun i => (P8 i : ℝ) / 8)) = (w.qR P8 R : ℝ) / 8 := by
  have hcast : ((w.num16 P8 R / 2 : ℤ) : ℝ) = (w.num16 P8 R : ℝ) / 2 := by
    rw [Int.cast_div heven (by norm_num)]; norm_num
  simp only [kdot, Rot.lin_apply, qR]
  rw [hcast]
  simp only [num16, y8]; push_cast; ring

lemma inv_e_apply (w : WaveSpec) (R : Rot) (i : Fin 3) : R.inv.lin (vec w.e) i = w.cR R i := by
  simp [Rot.lin_apply, cR]

/-- Exact field value at `x0 = P8 / 8` from integer data (checked by `decide` per instance). -/
theorem field_eighth (w : WaveSpec) (s : ℝ) (P8 : V)
    (heven : ∀ R ∈ Rot.R24, 2 ∣ w.num16 P8 R)
    (hB : ∀ i, ∑ R ∈ Rot.S24, cosB (w.qR P8 R) * w.cR R i = 0) (i : Fin 3) :
    w.field s (WithLp.toLp 2 fun j => (P8 j : ℝ) / 8) i =
      s * ((∑ R ∈ Rot.S24, cosA (w.qR P8 R) * w.cR R i : ℤ) : ℝ) := by
  have hsum : (∑ R ∈ Rot.S24, w.wave (R.lin (WithLp.toLp 2 fun j => (P8 j : ℝ) / 8)) •
      R.inv.lin (vec w.e)) i =
      ∑ R ∈ Rot.S24, (((cosA (w.qR P8 R) * w.cR R i : ℤ) : ℝ) +
        ((cosB (w.qR P8 R) * w.cR R i : ℤ) : ℝ) * (Real.sqrt 2 / 2)) := by
    rw [show (∑ R ∈ Rot.S24, w.wave (R.lin (WithLp.toLp 2 fun j => (P8 j : ℝ) / 8)) •
        R.inv.lin (vec w.e)) i = EuclideanSpace.proj i (∑ R ∈ Rot.S24,
          w.wave (R.lin (WithLp.toLp 2 fun j => (P8 j : ℝ) / 8)) • R.inv.lin (vec w.e)) from rfl,
      map_sum]
    refine Finset.sum_congr rfl fun R hR => ?_
    show (w.wave (R.lin (WithLp.toLp 2 fun j => (P8 j : ℝ) / 8)) • R.inv.lin (vec w.e)) i = _
    rw [PiLp.smul_apply, smul_eq_mul, w.inv_e_apply, wave,
      w.kdot_eighth P8 (heven R (Rot.mem_S24.mp hR)), cos_eighth]
    push_cast; ring
  rw [field, PiLp.smul_apply, smul_eq_mul, hsum, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Int.cast_sum, ← Int.cast_sum, hB i]
  simp

end WaveSpec
