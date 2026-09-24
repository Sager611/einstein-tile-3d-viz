import ChairWarp.Geometry

/-!
# Isometries whose powers all stay near the identity are the identity

Via von Neumann's mean ergodic theorem: if every iterate of a contraction `A` moves unit vectors by
at most `θ < 1`, the Birkhoff averages of `v` converge to a fixed point within `θ‖v‖` of `v`;
applying this to `v - lim` forces `v` itself to be fixed.
-/

open Filter Topology

lemma inv_nsmul_self {N : ℕ} (hN : 0 < N) (v : E) : (N : ℝ)⁻¹ • (N • v) = v := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN.ne'),
    one_smul]

lemma iter_sub (A : E →L[ℝ] E) (k : ℕ) (a b : E) : A^[k] (a - b) = A^[k] a - A^[k] b := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_sub]

lemma birkhoffAverage_sub_self (A : E →L[ℝ] E) {N : ℕ} (hN : 0 < N) (v : E) :
    birkhoffAverage ℝ A _root_.id N v - v =
      (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N, (A^[k] v - v) := by
  rw [birkhoffAverage, birkhoffSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    smul_sub, inv_nsmul_self hN]
  rfl

lemma norm_birkhoffAverage_sub_le (A : E →L[ℝ] E) {θ : ℝ} (hθ : 0 ≤ θ)
    (h : ∀ n v, ‖A^[n] v - v‖ ≤ θ * ‖v‖) {N : ℕ} (hN : 0 < N) (v : E) :
    ‖birkhoffAverage ℝ A _root_.id N v - v‖ ≤ θ * ‖v‖ := by
  rw [birkhoffAverage_sub_self A hN, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  calc (N : ℝ)⁻¹ * ‖∑ k ∈ Finset.range N, (A^[k] v - v)‖
      ≤ (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, ‖A^[k] v - v‖ := by gcongr; exact norm_sum_le _ _
    _ ≤ (N : ℝ)⁻¹ * ∑ _k ∈ Finset.range N, θ * ‖v‖ := by
        gcongr with k _; exact h k v
    _ = θ * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

lemma apply_birkhoffAverage (A : E →L[ℝ] E) (N : ℕ) (v : E) :
    A (birkhoffAverage ℝ A _root_.id N v) =
      birkhoffAverage ℝ A _root_.id N v + (N : ℝ)⁻¹ • (A^[N] v - v) := by
  have hcomm : ∀ k, A (A^[k] v) = A^[k] (A v) := fun k => by
    rw [← Function.iterate_succ_apply' A k v, Function.iterate_succ_apply]
  have hmap : A (birkhoffSum A _root_.id N v) = birkhoffSum A _root_.id N (A v) := by
    simp only [birkhoffSum, map_sum, _root_.id]
    exact Finset.sum_congr rfl fun k _ => hcomm k
  have key : A (birkhoffSum A _root_.id N v) = birkhoffSum A _root_.id N v + (A^[N] v - v) := by
    have := birkhoffSum_apply_sub_birkhoffSum (f := A) (g := _root_.id) N v
    simp only [_root_.id] at this
    rw [hmap, ← this]; abel
  simp only [birkhoffAverage]
  rw [map_smul, key, smul_add]

/-- A contraction all of whose iterates move vectors by at most `θ < 1` times their length is the
identity. -/
theorem fixed_of_iterates_near (A : E →L[ℝ] E) (hA : ‖A‖ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (h : ∀ n v, ‖A^[n] v - v‖ ≤ θ * ‖v‖) (v : E) : A v = v := by
  -- The Birkhoff averages of any `x` converge; call the limit `L x`.
  have conv := fun x => ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection A hA x
  set L : E → E := fun x => (A.eqLocus (1 : E →L[ℝ] E)).orthogonalProjectionOnto x
  -- the limit is fixed by `A`
  have hfix : ∀ x, A (L x) = L x := by
    intro x
    have h1 : Tendsto (fun N => A (birkhoffAverage ℝ A _root_.id N x)) atTop (𝓝 (A (L x))) :=
      (A.continuous.tendsto _).comp (conv x)
    have h2 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • (A^[N] x - x)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hg : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (θ * ‖x‖)) atTop (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (θ * ‖x‖)
      refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hg
      rw [norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (h N x) (inv_nonneg.mpr (Nat.cast_nonneg N))
    have h3 := (conv x).add h2
    rw [add_zero] at h3
    have : (fun N => A (birkhoffAverage ℝ A _root_.id N x)) =
        fun N => birkhoffAverage ℝ A _root_.id N x + (N : ℝ)⁻¹ • (A^[N] x - x) :=
      funext fun N => apply_birkhoffAverage A N x
    rw [this] at h1
    exact tendsto_nhds_unique h1 h3
  -- the limit is within `θ ‖x‖` of `x`
  have hclose : ∀ x, ‖L x - x‖ ≤ θ * ‖x‖ := by
    intro x
    have := ((conv x).sub_const x).norm
    refine le_of_tendsto this ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact norm_birkhoffAverage_sub_le A hθ0 h hN x
  -- apply to `w = v - L v`, whose averages converge to `L v - L v = 0`
  set w := v - L v
  have hw : Tendsto (fun N => birkhoffAverage ℝ A _root_.id N w) atTop (𝓝 0) := by
    have hlin : ∀ N, birkhoffAverage ℝ A _root_.id N w =
        birkhoffAverage ℝ A _root_.id N v - birkhoffAverage ℝ A _root_.id N (L v) := by
      intro N
      simp only [w, birkhoffAverage, birkhoffSum, _root_.id, iter_sub, Finset.sum_sub_distrib,
        smul_sub]
    have hconst : ∀ N, 0 < N → birkhoffAverage ℝ A _root_.id N (L v) = L v := by
      intro N hN
      have : ∀ k, A^[k] (L v) = L v := fun k => Function.iterate_fixed (hfix v) k
      simp only [birkhoffAverage, birkhoffSum, _root_.id, this, Finset.sum_const,
        Finset.card_range]
      exact inv_nsmul_self hN _
    have : Tendsto (fun N => birkhoffAverage ℝ A _root_.id N v - birkhoffAverage ℝ A _root_.id N (L v))
        atTop (𝓝 (L v - L v)) := by
      refine (conv v).sub ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      exact (hconst N hN).symm
    rw [sub_self] at this
    exact this.congr fun N => (hlin N).symm
  have hwle : ‖w‖ ≤ θ * ‖w‖ := by
    have := (hw.sub_const w).norm
    rw [zero_sub, norm_neg] at this
    refine le_of_tendsto this ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact norm_birkhoffAverage_sub_le A hθ0 h hN w
  have hw0 : w = 0 := by
    have : ‖w‖ ≤ 0 := by nlinarith [norm_nonneg w]
    exact norm_le_zero_iff.mp this
  have hv : v = L v := sub_eq_zero.mp hw0
  rw [hv]; exact hfix v

lemma iter_smul (A : E →L[ℝ] E) (k : ℕ) (t : ℝ) (a : E) : A^[k] (t • a) = t • A^[k] a := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_smul]

lemma pow_succ_apply (σ : E ≃ᵢ E) (n : ℕ) (x : E) : (σ ^ (n + 1)) x = σ ((σ ^ n) x) := by
  rw [pow_succ']; rfl

/-- An isometry of `ℝ³` all of whose powers move the unit ball around `c0` by less than `1/2` is the
identity. -/
theorem isometry_eq_one_of_near (σ : E ≃ᵢ E) (c0 : E) {C : ℝ} (hC0 : 0 ≤ C) (hC : C < 1 / 2)
    (h : ∀ n : ℕ, ∀ x, ‖x - c0‖ ≤ 1 → ‖(σ ^ n) x - x‖ ≤ C) : σ = 1 := by
  -- linear part via Mazur–Ulam
  let τ : E ≃ᵢ E := σ.trans (IsometryEquiv.addRight (-σ 0))
  have hτ0 : τ 0 = 0 := by simp [τ]
  let Aℓ := τ.toRealLinearIsometryEquivOfMapZero hτ0
  have hAℓ : ∀ x, Aℓ x = σ x - σ 0 := fun x => by
    simp [Aℓ, τ, sub_eq_add_neg]
  let A : E →L[ℝ] E := Aℓ.toLinearIsometry.toContinuousLinearMap
  have hA : ∀ x, A x = σ x - σ 0 := hAℓ
  have hAnorm : ‖A‖ ≤ 1 := Aℓ.toLinearIsometry.norm_toContinuousLinearMap_le
  have hdiff : ∀ x y, σ x - σ y = A (x - y) := fun x y => by
    rw [map_sub, hA, hA]; abel
  have hiter : ∀ n x y, (σ ^ n) x - (σ ^ n) y = A^[n] (x - y) := by
    intro n
    induction n with
    | zero => intro x y; rfl
    | succ n ih =>
      intro x y
      rw [pow_succ_apply, pow_succ_apply, hdiff, ih, Function.iterate_succ_apply']
  -- iterates of `A` move unit vectors by at most `2C`
  have hunit : ∀ n v, ‖v‖ ≤ 1 → ‖A^[n] v - v‖ ≤ 2 * C := by
    intro n v hv
    have h1 := h n (c0 + v) (by simpa using hv)
    have h2 := h n c0 (by simp)
    have : A^[n] v - v = ((σ ^ n) (c0 + v) - (c0 + v)) - ((σ ^ n) c0 - c0) := by
      have e := hiter n (c0 + v) c0
      rw [add_sub_cancel_left] at e
      rw [← e]; abel
    rw [this]
    calc _ ≤ ‖(σ ^ n) (c0 + v) - (c0 + v)‖ + ‖(σ ^ n) c0 - c0‖ := norm_sub_le _ _
      _ ≤ 2 * C := by linarith
  have hall : ∀ n v, ‖A^[n] v - v‖ ≤ 2 * C * ‖v‖ := by
    intro n v
    rcases eq_or_ne v 0 with rfl | hv
    · have h0 : A^[n] (0 : E) = 0 := by simpa using iter_smul A n 0 0
      simp [h0]
    · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      set u := ‖v‖⁻¹ • v
      have hu : ‖u‖ ≤ 1 := by
        simp [u, norm_smul, inv_mul_cancel₀ hn.ne']
      have hvu : v = ‖v‖ • u := by simp [u, smul_smul, mul_inv_cancel₀ hn.ne']
      have hbound := hunit n u hu
      have e : A^[n] v - v = ‖v‖ • (A^[n] u - u) := by
        conv_lhs => rw [hvu]
        rw [iter_smul, smul_sub]
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hn]
      calc ‖v‖ * ‖A^[n] u - u‖ ≤ ‖v‖ * (2 * C) := mul_le_mul_of_nonneg_left hbound hn.le
        _ = 2 * C * ‖v‖ := by ring
  have hAid : ∀ v, A v = v :=
    fixed_of_iterates_near A hAnorm (by linarith) (by linarith) hall
  -- so `σ` is a translation by `b = σ 0`
  set b := σ 0
  have htrans : ∀ x, σ x = x + b := fun x => by
    have := hA x
    rw [hAid, eq_sub_iff_add_eq] at this
    exact this.symm
  have hpow : ∀ n : ℕ, ∀ x, (σ ^ n) x = x + (n : ℝ) • b := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ_apply, htrans, ih]; push_cast; rw [add_smul, one_smul]; abel
  have hb : b = 0 := by
    by_contra hb
    have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
    obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖b‖)
    have := h n c0 (by simp)
    rw [hpow, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, Nat.abs_cast] at this
    rw [div_lt_iff₀ hbn] at hn
    linarith
  ext x : 1
  rw [htrans, hb, add_zero]; rfl
