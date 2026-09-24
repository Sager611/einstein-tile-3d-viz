import ChairWarp.Geometry

/-!
# A concrete `Γ`-equivariant warp of Euclidean 3-space

`field x = ε • ∑_{R ∈ R24} cos (2π k·(R x)) • R⁻¹ e₁` with `k = (1, 1/2, 1/2)`, `e₁ = (1,1,0)` and
`ε = 1/10⁹`. It is periodic under the body-centred lattice (because `k·b ∈ ℤ` for `b ∈ BCC`) and
rotation-equivariant (by averaging over the group), so `Φ = id + field` commutes with every motion
of `GammaGeom`.
-/

open Real
open scoped BigOperators

namespace Rot

/-- The 24 rotations as a finset. -/
def S24 : Finset Rot := R24.toFinset

lemma mem_S24 {r : Rot} : r ∈ S24 ↔ r ∈ R24 := List.mem_toFinset

lemma S24_card : S24.card = 24 := by decide +kernel

lemma comp_inv_cancel_right :
    ∀ R ∈ R24, ∀ S ∈ R24, (R.comp S).comp S.inv = R := by decide +kernel

lemma comp_inv_comp : ∀ R ∈ R24, ∀ S ∈ R24, S.comp (R.comp S).inv = R.inv := by decide +kernel

lemma inv_inv_eq : ∀ S ∈ R24, S.inv.inv = S := by decide +kernel

lemma lin_vec (r : Rot) (t : V) : r.lin (vec t) = vec (r.act t) := by
  ext i; simp [Rot.act]

end Rot

/-- `k · y` for `k = (1, 1/2, 1/2)`; `k · b ∈ ℤ` for every body-centred lattice vector `b`. -/
noncomputable def kdot (y : E) : ℝ := y 0 + (y 1 + y 2) / 2

/-- A chiral wave: with this `k` and `e₁` the averaged field has non-zero normal components on the
grid faces, so the warp genuinely bends the faces of Chair44. -/
noncomputable def wave (y : E) : ℝ := Real.cos (2 * π * kdot y)

noncomputable def e1 : E := WithLp.toLp 2 ![1, 1, 0]

noncomputable def eps : ℝ := 1 / 10 ^ 9

noncomputable def field (x : E) : E :=
  eps • ∑ R ∈ Rot.S24, wave (R.lin x) • R.inv.lin e1

noncomputable def warpFun (x : E) : E := x + field x

lemma kdot_add (y z : E) : kdot (y + z) = kdot y + kdot z := by
  simp [kdot]; ring

lemma wave_add_bcc (y : E) {c : V} (hc : bcc c) : wave (y + vec c) = wave y := by
  obtain ⟨m, hm⟩ := hc.2
  have hk : kdot (vec c) = ((c 0 + c 2 + m : ℤ) : ℝ) := by
    simp only [kdot, vec_apply]; push_cast
    have : (c 1 : ℝ) = c 2 + 2 * m := by exact_mod_cast (by omega : c 1 = c 2 + 2 * m)
    rw [this]; ring
  rw [wave, wave, kdot_add, hk, mul_add]
  have : 2 * π * ((c 0 + c 2 + m : ℤ) : ℝ) = ((c 0 + c 2 + m : ℤ) : ℝ) * (2 * π) := by ring
  rw [this, Real.cos_add_int_mul_two_pi]

/-- Periodicity under the body-centred lattice. -/
lemma field_add_bcc (x : E) {t : V} (ht : bcc t) : field (x + vec t) = field x := by
  unfold field
  congr 1
  refine Finset.sum_congr rfl fun R hR => ?_
  rw [map_add, Rot.lin_vec, wave_add_bcc _ (bcc_act (Rot.mem_S24.mp hR) ht)]

/-- Rotation equivariance, by reindexing the group average. -/
lemma field_rot {S : Rot} (hS : S ∈ Rot.R24) (x : E) : field (S.lin x) = S.lin (field x) := by
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
    have hQ' := Rot.mem_S24.mp hQ
    have hSi := (Rot.inv_spec S hS)
    -- (Q ∘ S⁻¹) ∘ S = Q
    show (Q.comp S.inv).comp S = Q
    have h1 := Rot.comp_inv_cancel_right Q hQ' S.inv hSi.1
    rw [Rot.inv_inv_eq S hS] at h1; exact h1
  · intro R hR
    have hR' := Rot.mem_S24.mp hR
    rw [map_smul, ← Rot.lin_comp, ← Rot.lin_comp, Rot.comp_inv_comp R hR' S hS]

/-- `Φ` commutes with every pose of `Γ`. -/
lemma warpFun_pose (P : Pose) (hP : P.InGamma) (x : E) :
    warpFun (P.toFun x) = P.toFun (warpFun x) := by
  simp only [warpFun, Pose.toFun]
  rw [field_add_bcc _ hP.2, field_rot hP.1, map_add]
  abel

/-! ## Lipschitz bound and the homeomorphism -/

lemma kdot_sub (y z : E) : kdot y - kdot z = kdot (y - z) := by
  simp [kdot]; ring

lemma abs_kdot_le (z : E) : |kdot z| ≤ 2 * ‖z‖ := by
  have h0 := PiLp.norm_apply_le z 0
  have h1 := PiLp.norm_apply_le z 1
  have h2 := PiLp.norm_apply_le z 2
  simp only [Real.norm_eq_abs] at h0 h1 h2
  unfold kdot
  have := abs_add_le (z 0) ((z 1 + z 2) / 2)
  have : |(z 1 + z 2) / 2| ≤ (|z 1| + |z 2|) / 2 := by
    rw [abs_div, abs_two]; gcongr; exact abs_add_le _ _
  linarith

lemma norm_e1 : ‖e1‖ ≤ 3 / 2 := by
  have h : ‖e1‖ ^ 2 = 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [e1, Fin.sum_univ_three]; norm_num
  nlinarith [norm_nonneg e1]

lemma norm_term_sub {R : Rot} (hR : R ∈ Rot.R24) (x y : E) :
    ‖wave (R.lin x) • R.inv.lin e1 - wave (R.lin y) • R.inv.lin e1‖ ≤ 6 * π * ‖x - y‖ := by
  rw [← sub_smul, norm_smul, Rot.norm_lin (Rot.inv_spec R hR).1, Real.norm_eq_abs]
  have hw : |wave (R.lin x) - wave (R.lin y)| ≤ 4 * π * ‖x - y‖ :=
    calc |wave (R.lin x) - wave (R.lin y)|
        ≤ |2 * π * kdot (R.lin x) - 2 * π * kdot (R.lin y)| := Real.abs_cos_sub_cos_le _ _
      _ = 2 * π * |kdot (R.lin (x - y))| := by
          rw [← mul_sub, kdot_sub, ← map_sub, abs_mul, abs_of_pos (by positivity)]
      _ ≤ 2 * π * (2 * ‖R.lin (x - y)‖) := by gcongr; exact abs_kdot_le _
      _ = 4 * π * ‖x - y‖ := by rw [Rot.norm_lin hR]; ring
  have he := norm_e1
  have hn := norm_nonneg (x - y)
  calc |wave (R.lin x) - wave (R.lin y)| * ‖e1‖ ≤ (4 * π * ‖x - y‖) * (3 / 2) :=
        mul_le_mul hw he (norm_nonneg _) (by positivity)
    _ = 6 * π * ‖x - y‖ := by ring

theorem field_lipschitz (x y : E) : ‖field x - field y‖ ≤ (1 / 5) * ‖x - y‖ := by
  unfold field
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul]
  have hsum : ‖∑ R ∈ Rot.S24, (wave (R.lin x) • R.inv.lin e1 - wave (R.lin y) • R.inv.lin e1)‖
      ≤ 24 * (6 * π * ‖x - y‖) := by
    calc _ ≤ ∑ R ∈ Rot.S24, ‖wave (R.lin x) • R.inv.lin e1 - wave (R.lin y) • R.inv.lin e1‖ :=
          norm_sum_le _ _
      _ ≤ Rot.S24.card • (6 * π * ‖x - y‖) :=
          Finset.sum_le_card_nsmul _ _ _ fun R hR => norm_term_sub (Rot.mem_S24.mp hR) x y
      _ = 24 * (6 * π * ‖x - y‖) := by rw [Rot.S24_card]; simp
  have hε : ‖eps‖ = 1 / 10 ^ 9 := by simp [eps]
  rw [hε]
  have hπ := Real.pi_le_four
  have hn := norm_nonneg (x - y)
  calc 1 / 10 ^ 9 * ‖_‖ ≤ 1 / 10 ^ 9 * (24 * (6 * π * ‖x - y‖)) := by gcongr
    _ ≤ 1 / 5 * ‖x - y‖ := by nlinarith

open scoped NNReal in
theorem warpFun_approx :
    ApproximatesLinearOn warpFun
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) Set.univ (1 / 5 : ℝ≥0) := by
  intro x _ y _
  have : warpFun x - warpFun y - (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) (x - y) =
      field x - field y := by
    simp [warpFun]; abel
  rw [this]
  simpa using field_lipschitz x y

/-- The warp `Φ = id + field` as a homeomorphism of `E`. -/
noncomputable def warp : E ≃ₜ E :=
  warpFun_approx.toHomeomorph warpFun (Or.inr (by
    simp [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.nnnorm_id]
    norm_num))

@[simp] lemma warp_apply (x : E) : warp x = warpFun x := rfl

/-- `Φ` commutes with every element of Chair44's motion group. -/
theorem warp_comm : ∀ γ ∈ GammaGeom, ∀ x, warp (γ x) = γ (warp x) := by
  intro γ hγ
  induction hγ using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨P, hP, rfl⟩ := hg
    intro x
    simp [warpFun_pose P hP]
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

/-! ## An exact value: the warp pushes a face point off its plane

At `x0 = (3/4, 1/2, 0)` every phase `k · R x0` is a multiple of `1/8`, so each cosine is
`A + B · √2/2` with integers `A, B`; the `√2` parts cancel and `field x0 = ε · (0, 0, -4)`. -/

noncomputable def x0 : E := WithLp.toLp 2 ![3 / 4, 1 / 2, 0]

/-- `8 · x0` as an integer vector. -/
def P8 : V := ![6, 4, 0]

lemma x0_apply (j : Fin 3) : x0 j = (P8 j : ℝ) / 8 := by
  fin_cases j <;> simp [x0, P8] <;> norm_num

/-- `8 · (R x0)`. -/
def y8 (R : Rot) (j : Fin 3) : ℤ := R.s j * P8 (R.p j)

lemma y8_even : ∀ R ∈ Rot.R24, 2 ∣ y8 R 1 + y8 R 2 := by decide +kernel

/-- Integer phase numerator: `k · (R x0) = qR R / 8`. -/
def qR (R : Rot) : ℤ := y8 R 0 + (y8 R 1 + y8 R 2) / 2

/-- `cos (q π / 4) = cosA q + cosB q · √2/2`. -/
def cosA (q : ℤ) : ℤ :=
  match q % 8 with
  | 0 => 1 | 4 => -1 | _ => 0

def cosB (q : ℤ) : ℤ :=
  match q % 8 with
  | 1 => 1 | 7 => 1 | 3 => -1 | 5 => -1 | _ => 0

lemma cos_eighth (q : ℤ) :
    Real.cos (2 * π * ((q : ℝ) / 8)) = cosA q + cosB q * (Real.sqrt 2 / 2) := by
  have hq : q = 8 * (q / 8) + q % 8 := by omega
  have hr0 : 0 ≤ q % 8 := Int.emod_nonneg q (by norm_num)
  have hr8 : q % 8 < 8 := Int.emod_lt_of_pos q (by norm_num)
  have harg : 2 * π * ((q : ℝ) / 8) = ((q % 8 : ℤ) : ℝ) * (π / 4) + ((q / 8 : ℤ) : ℝ) * (2 * π) := by
    conv_lhs => rw [hq]
    push_cast; ring
  rw [harg, Real.cos_add_int_mul_two_pi]
  have c4 := Real.cos_pi_div_four
  interval_cases h : q % 8 <;> simp only [cosA, cosB, h] <;> push_cast
  · simp
  · rw [one_mul]; simp [c4]
  · rw [show (2 : ℝ) * (π / 4) = π / 2 by ring, Real.cos_pi_div_two]; simp
  · rw [show (3 : ℝ) * (π / 4) = π - π / 4 by ring, Real.cos_pi_sub, c4]; ring
  · rw [show (4 : ℝ) * (π / 4) = π by ring, Real.cos_pi]; simp
  · rw [show (5 : ℝ) * (π / 4) = π / 4 + π by ring, Real.cos_add_pi, c4]; ring
  · rw [show (6 : ℝ) * (π / 4) = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two]; simp
  · rw [show (7 : ℝ) * (π / 4) = -(π / 4) + ((1 : ℤ) : ℝ) * (2 * π) by push_cast; ring,
      Real.cos_add_int_mul_two_pi, Real.cos_neg, c4]; ring

lemma kdot_x0 {R : Rot} (hR : R ∈ Rot.R24) : kdot (R.lin x0) = (qR R : ℝ) / 8 := by
  have hdiv := y8_even R hR
  have hcast : (((y8 R 1 + y8 R 2) / 2 : ℤ) : ℝ) = ((y8 R 1 + y8 R 2 : ℤ) : ℝ) / 2 := by
    rw [Int.cast_div hdiv (by norm_num)]; norm_num
  simp only [kdot, Rot.lin_apply, x0_apply, qR]
  push_cast
  rw [hcast]
  simp only [y8]; push_cast; ring

/-- Integer coordinates of `R⁻¹ e₁`. -/
def cR (R : Rot) (i : Fin 3) : ℤ := R.inv.s i * (![1, 1, 0] : V) (R.inv.p i)

lemma inv_e1_apply (R : Rot) (i : Fin 3) : R.inv.lin e1 i = cR R i := by
  simp only [Rot.lin_apply, cR, e1]
  push_cast
  generalize R.inv.p i = j
  fin_cases j <;> simp

lemma certificate :
    (∀ i, ∑ R ∈ Rot.S24, cosB (qR R) * cR R i = 0) ∧
      ∑ R ∈ Rot.S24, cosA (qR R) * cR R 0 = 0 ∧ ∑ R ∈ Rot.S24, cosA (qR R) * cR R 1 = 0 ∧
      ∑ R ∈ Rot.S24, cosA (qR R) * cR R 2 = -4 := by
  decide +kernel

theorem field_x0 (i : Fin 3) :
    field x0 i = eps * ((∑ R ∈ Rot.S24, cosA (qR R) * cR R i : ℤ) : ℝ) := by
  have hsum : (∑ R ∈ Rot.S24, wave (R.lin x0) • R.inv.lin e1) i =
      ∑ R ∈ Rot.S24, (((cosA (qR R) * cR R i : ℤ) : ℝ) +
        ((cosB (qR R) * cR R i : ℤ) : ℝ) * (Real.sqrt 2 / 2)) := by
    rw [show (∑ R ∈ Rot.S24, wave (R.lin x0) • R.inv.lin e1) i =
        EuclideanSpace.proj i (∑ R ∈ Rot.S24, wave (R.lin x0) • R.inv.lin e1) from rfl, map_sum]
    refine Finset.sum_congr rfl fun R hR => ?_
    show (wave (R.lin x0) • R.inv.lin e1) i = _
    rw [PiLp.smul_apply, smul_eq_mul, inv_e1_apply, wave, kdot_x0 (Rot.mem_S24.mp hR), cos_eighth]
    push_cast; ring
  rw [field, PiLp.smul_apply, smul_eq_mul, hsum, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Int.cast_sum, ← Int.cast_sum, certificate.1 i]
  simp

/-- The warp moves `x0 = (3/4, 1/2, 0)` straight off the face `z = 0`: `warp x0 = (3/4, 1/2, -4ε)`. -/
theorem warp_x0 : warp x0 = x0 + eps • (WithLp.toLp 2 ![0, 0, -4] : E) := by
  obtain ⟨_, h0, h1, h2⟩ := certificate
  ext i
  simp only [warp_apply, warpFun, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, field_x0]
  fin_cases i <;> simp [h0, h1, h2]

theorem warp_ne_id : warp x0 ≠ x0 := by
  intro h
  have := congrArg (fun z : E => z 2) h
  simp only [warp_x0, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at this
  simp [eps] at this

/-- The warp moves every point by at most `36 ε`. -/
theorem norm_warp_sub_le (x : E) : ‖warp x - x‖ ≤ 36 * eps := by
  rw [warp_apply, warpFun, add_sub_cancel_left, field, norm_smul]
  have hε : ‖eps‖ = eps := by simp [eps]
  rw [hε]
  have hsum : ‖∑ R ∈ Rot.S24, wave (R.lin x) • R.inv.lin e1‖ ≤ 36 := by
    calc _ ≤ ∑ R ∈ Rot.S24, ‖wave (R.lin x) • R.inv.lin e1‖ := norm_sum_le _ _
      _ ≤ Rot.S24.card • (3 / 2 : ℝ) := by
          refine Finset.sum_le_card_nsmul _ _ _ fun R hR => ?_
          rw [norm_smul, Rot.norm_lin (Rot.inv_spec R (Rot.mem_S24.mp hR)).1, Real.norm_eq_abs]
          calc |wave (R.lin x)| * ‖e1‖ ≤ 1 * (3 / 2) :=
                mul_le_mul (Real.abs_cos_le_one _) norm_e1 (norm_nonneg _) zero_le_one
            _ = 3 / 2 := one_mul _
      _ = 36 := by rw [Rot.S24_card]; norm_num
  have : (0 : ℝ) ≤ eps := by simp [eps]
  nlinarith
