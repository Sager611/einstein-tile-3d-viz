import ChairWarp.Diam

/-!
# Near-symmetries of Chair44 are near the identity

`NearSym d σ`: `σ` moves every point of `Q` to within `d` of `Q`. For small `d` we show
`‖σ x - x‖ ≤ 300 d` on the box: corners pin `σ` to one of the 12 symmetries of the box fixing the
diagonal; the six that swap its ends are excluded because `Q` stays away from `(2,2,2)`, and the
five non-trivial axis permutations are excluded by the feature probes.
-/

def NearSym (d : ℝ) (σ : E ≃ᵢ E) : Prop := ∀ q ∈ Q, ∃ q' ∈ Q, ‖σ q - q'‖ ≤ d

/-! ## Integer corner data -/

def sqd (w w' : V) : ℤ := (w 0 - w' 0) ^ 2 + (w 1 - w' 1) ^ 2 + (w 2 - w' 2) ^ 2

def V6l : List V := [![2, 0, 0], ![0, 2, 0], ![0, 0, 2], ![0, 2, 2], ![2, 0, 2], ![2, 2, 0]]

lemma mem_V6l {w : V} (hw : IsCorner6 w) : w ∈ V6l := by
  obtain ⟨hc, ⟨i, hi⟩, ⟨j, hj⟩⟩ := hw
  have e : w = ![w 0, w 1, w 2] := by funext k; fin_cases k <;> rfl
  rw [e]; clear e
  rcases hc 0 with h0 | h0 <;> rcases hc 1 with h1 | h1 <;> rcases hc 2 with h2 | h2 <;>
    rw [h0, h1, h2] <;>
    first
    | decide
    | (exfalso; fin_cases i <;> fin_cases j <;> simp_all)

lemma isCorner6_of_mem {w : V} (hw : w ∈ V6l) : IsCorner6 w := by
  simp only [V6l, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨fun i => by fin_cases i <;> simp, by decide, by decide⟩

def a1 : V := ![2, 0, 0]
def a2 : V := ![0, 2, 0]
def a3 : V := ![0, 0, 2]
def a4 : V := ![0, 2, 2]

/-- The 12 symmetries of the box preserving the diagonal `{(0,0,0),(2,2,2)}`. -/
def syms : List Pose :=
  (Rot.perms.map fun p => (⟨⟨p, ![1, 1, 1]⟩, 0⟩ : Pose)) ++
    (Rot.perms.map fun p => (⟨⟨p, ![-1, -1, -1]⟩, ![2, 2, 2]⟩ : Pose))

def Pose.actV (P : Pose) (v : V) : V := P.r.act v + P.t

lemma four_corners : ∀ w1 ∈ V6l, ∀ w2 ∈ V6l, ∀ w3 ∈ V6l, ∀ w4 ∈ V6l,
    sqd w1 w2 = 8 → sqd w1 w3 = 8 → sqd w2 w3 = 8 → sqd w1 w4 = 12 → sqd w2 w4 = 4 →
    sqd w3 w4 = 4 → ∃ B ∈ syms, B.actV a1 = w1 ∧ B.actV a2 = w2 ∧ B.actV a3 = w3 ∧ B.actV a4 = w4 := by
  decide +kernel

def idPose : Pose := ⟨Rot.id, 0⟩

/-- Each box symmetry is the identity, swaps the diagonal's ends, or is a permutation with a probe. -/
lemma syms_kind : ∀ B ∈ syms, (B.r = Rot.id ∧ B.t = 0) ∨ B.actV 0 = ![2, 2, 2] ∨
    ∃ pr ∈ probes, B.r.s = ![1, 1, 1] ∧ B.t = 0 ∧ B.r.p = pr.p := by
  decide +kernel

lemma toFun_vec (P : Pose) (v : V) : P.toFun (vec v) = vec (P.actV v) := by
  ext i; simp [Pose.toFun, Pose.actV, Rot.act]

lemma vec_sub (v w : V) : vec v - vec w = vec (v - w) := by ext i; simp

lemma norm_sq_vec (v : V) : ‖vec v‖ ^ 2 = ((v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 : ℤ) : ℝ) := by
  rw [norm_sq_three]; simp

lemma norm_sq_vec_sub (v w : V) : ‖vec v - vec w‖ ^ 2 = (sqd v w : ℝ) := by
  rw [vec_sub, norm_sq_vec]; simp [sqd]

/-! ## Linear part of an isometry -/

lemma exists_linear (σ : E ≃ᵢ E) : ∃ A : E →L[ℝ] E, ∀ x y, σ x - σ y = A (x - y) := by
  let τ : E ≃ᵢ E := σ.trans (IsometryEquiv.addRight (-σ 0))
  have hτ0 : τ 0 = 0 := by simp [τ]
  let Aℓ := τ.toRealLinearIsometryEquivOfMapZero hτ0
  have hA : ∀ x, Aℓ x = σ x - σ 0 := fun x => by simp [Aℓ, τ, sub_eq_add_neg]
  refine ⟨Aℓ.toLinearIsometry.toContinuousLinearMap, fun x y => ?_⟩
  show σ x - σ y = Aℓ (x - y)
  rw [map_sub, hA, hA]; abel

/-! ## Corner images -/

section
variable {d : ℝ} {σ : E ≃ᵢ E}

lemma corner_image (hd0 : 0 ≤ d) (hd : d ≤ 1 / 10 ^ 6) (hN : NearSym d σ) {v : V}
    (hv : IsCorner6 v) : ∃ w : V, IsCorner6 w ∧ ‖σ (vec v) - vec w‖ ≤ 22 * d := by
  let vs : V := fun i => 2 - v i
  have hvs : IsCorner6 vs := by
    obtain ⟨hc, ⟨i, hi⟩, ⟨j, hj⟩⟩ := hv
    exact ⟨fun k => by rcases hc k with h | h <;> simp [vs, h], ⟨j, by simp [vs, hj]⟩,
      ⟨i, by simp [vs, hi]⟩⟩
  have mem : ∀ u : V, IsCorner6 u → vec u ∈ Q := fun u hu =>
    corner_mem u hu.1 hu.2.1
  obtain ⟨q, hq, hq1⟩ := hN _ (mem v hv)
  obtain ⟨q', hq', hq2⟩ := hN _ (mem vs hvs)
  -- the two corners are √12 apart
  set s := ‖vec v - vec vs‖
  have hs2 : s ^ 2 = 12 := by
    rw [norm_sq_vec_sub]
    obtain ⟨hc, _, _⟩ := hv
    have : sqd v vs = 12 := by
      simp only [sqd, vs]
      rcases hc 0 with h0 | h0 <;> rcases hc 1 with h1 | h1 <;> rcases hc 2 with h2 | h2 <;>
        simp [h0, h1, h2]
    rw [this]; norm_num
  have hs0 : 0 ≤ s := norm_nonneg _
  have hs35 : s ≤ 7 / 2 := by nlinarith
  have hσ : ‖σ (vec v) - σ (vec vs)‖ = s := by rw [← dist_eq_norm, σ.dist_eq, dist_eq_norm]
  have hqq : s - 2 * d ≤ ‖q - q'‖ := by
    have := norm_sub_le (σ (vec v) - q) (σ (vec vs) - q')
    have e : σ (vec v) - σ (vec vs) = (σ (vec v) - q) - (σ (vec vs) - q') + (q - q') := by abel
    have := norm_add_le ((σ (vec v) - q) - (σ (vec vs) - q')) (q - q')
    rw [← e, hσ] at this
    have := norm_sub_le (σ (vec v) - q) (σ (vec vs) - q')
    linarith
  have hsq : 12 - 14 * d ≤ ‖q - q'‖ ^ 2 := by
    have h2 : 0 ≤ s - 2 * d := by nlinarith
    nlinarith [pow_le_pow_left₀ h2 hqq 2]
  obtain ⟨w, hw, hwq⟩ := near_diametral hq hq' (by positivity) (by nlinarith) hsq
  refine ⟨w, hw, ?_⟩
  have hqw : ‖q - vec w‖ ≤ 21 * d := by
    refine (norm_le_sum_abs _).trans ?_
    simp only [PiLp.sub_apply, vec_apply]
    have := hwq 0; have := hwq 1; have := hwq 2
    linarith
  calc ‖σ (vec v) - vec w‖ = ‖(σ (vec v) - q) + (q - vec w)‖ := by congr 1; abel
    _ ≤ ‖σ (vec v) - q‖ + ‖q - vec w‖ := norm_add_le _ _
    _ ≤ 22 * d := by linarith

/-- Images of corners at integer squared distance: the squared distance is preserved exactly. -/
lemma sqd_preserved (hd0 : 0 ≤ d) (hd : d ≤ 1 / 10 ^ 6) {v v' w w' : V}
    (hv : ‖σ (vec v) - vec w‖ ≤ 22 * d) (hv' : ‖σ (vec v') - vec w'‖ ≤ 22 * d)
    (hvn : sqd v v' ≤ 12) (hwn : sqd w w' ≤ 12) : sqd w w' = sqd v v' := by
  set a := ‖vec w - vec w'‖; set b := ‖vec v - vec v'‖
  have ha2 : a ^ 2 = sqd w w' := norm_sq_vec_sub w w'
  have hb2 : b ^ 2 = sqd v v' := norm_sq_vec_sub v v'
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have ha4 : a ≤ 4 := by
    have : (sqd w w' : ℝ) ≤ 12 := by exact_mod_cast hwn
    nlinarith
  have hb4 : b ≤ 4 := by
    have : (sqd v v' : ℝ) ≤ 12 := by exact_mod_cast hvn
    nlinarith
  have hσ : ‖σ (vec v) - σ (vec v')‖ = b := by rw [← dist_eq_norm, σ.dist_eq, dist_eq_norm]
  set X := σ (vec v) - σ (vec v')
  have h1 : a ≤ b + 44 * d := by
    have e1 : vec w - vec w' = (X - (σ (vec v) - vec w)) + (σ (vec v') - vec w') := by
      simp only [X]; abel
    calc a = ‖(X - (σ (vec v) - vec w)) + (σ (vec v') - vec w')‖ := by rw [← e1]
      _ ≤ ‖X - (σ (vec v) - vec w)‖ + ‖σ (vec v') - vec w'‖ := norm_add_le _ _
      _ ≤ (‖X‖ + ‖σ (vec v) - vec w‖) + ‖σ (vec v') - vec w'‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ b + 44 * d := by rw [hσ]; linarith
  have h2 : b ≤ a + 44 * d := by
    have e2 : X = ((vec w - vec w') + (σ (vec v) - vec w)) - (σ (vec v') - vec w') := by
      simp only [X]; abel
    calc b = ‖X‖ := hσ.symm
      _ = ‖((vec w - vec w') + (σ (vec v) - vec w)) - (σ (vec v') - vec w')‖ := by rw [← e2]
      _ ≤ ‖(vec w - vec w') + (σ (vec v) - vec w)‖ + ‖σ (vec v') - vec w'‖ := norm_sub_le _ _
      _ ≤ (a + ‖σ (vec v) - vec w‖) + ‖σ (vec v') - vec w'‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ a + 44 * d := by linarith
  have hab : |a - b| ≤ 44 * d := by rw [abs_le]; constructor <;> linarith
  have hdiff : |(sqd w w' : ℝ) - sqd v v'| < 1 := by
    rw [← ha2, ← hb2, show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul]
    have : |a + b| ≤ 8 := by rw [abs_of_nonneg (by positivity)]; linarith
    calc |a - b| * |a + b| ≤ 44 * d * 8 := mul_le_mul hab this (abs_nonneg _) (by positivity)
      _ < 1 := by nlinarith
  have : |((sqd w w' - sqd v v' : ℤ) : ℝ)| < 1 := by push_cast; exact hdiff
  have hz : |sqd w w' - sqd v v'| < 1 := by exact_mod_cast this
  have := abs_lt.mp hz
  omega

end

lemma sqd_corner_le : ∀ w ∈ V6l, ∀ w' ∈ V6l, sqd w w' ≤ 12 := by decide +kernel

lemma controls : IsCorner6 a1 ∧ IsCorner6 a2 ∧ IsCorner6 a3 ∧ IsCorner6 a4 :=
  ⟨isCorner6_of_mem (by decide), isCorner6_of_mem (by decide), isCorner6_of_mem (by decide),
    isCorner6_of_mem (by decide)⟩

lemma control_sqd : sqd a1 a2 = 8 ∧ sqd a1 a3 = 8 ∧ sqd a2 a3 = 8 ∧ sqd a1 a4 = 12 ∧
    sqd a2 a4 = 4 ∧ sqd a3 a4 = 4 := by decide

lemma barycentric (x : E) :
    x - vec a1 = ((x 1) / 2 - ((x 0 + x 1 + x 2) / 2 - 1)) • (vec a2 - vec a1) +
      ((x 2) / 2 - ((x 0 + x 1 + x 2) / 2 - 1)) • (vec a3 - vec a1) +
      ((x 0 + x 1 + x 2) / 2 - 1) • (vec a4 - vec a1) := by
  ext i
  fin_cases i <;> simp [a1, a2, a3, a4] <;> ring

section
variable {d : ℝ} {σ : E ≃ᵢ E}

/-- **Pinning.** A near-symmetry of Chair44 is within `300 d` of the identity on the box. -/
theorem near_id_on_box (hd0 : 0 ≤ d) (hd7 : d ≤ 1 / 10 ^ 7) (hN : NearSym d σ) (x : E)
    (hx : ∀ i, -1 / 100 ≤ x i ∧ x i ≤ 2 + 1 / 100) : ‖σ x - x‖ ≤ 300 * d := by
  have hd : d ≤ 1 / 10 ^ 6 := hd7.trans (by norm_num)
  obtain ⟨c1, c2, c3, c4⟩ := controls
  obtain ⟨w1, hw1, e1⟩ := corner_image hd0 hd hN c1
  obtain ⟨w2, hw2, e2⟩ := corner_image hd0 hd hN c2
  obtain ⟨w3, hw3, e3⟩ := corner_image hd0 hd hN c3
  obtain ⟨w4, hw4, e4⟩ := corner_image hd0 hd hN c4
  have m1 := mem_V6l hw1; have m2 := mem_V6l hw2; have m3 := mem_V6l hw3; have m4 := mem_V6l hw4
  have la1 := mem_V6l c1; have la2 := mem_V6l c2; have la3 := mem_V6l c3; have la4 := mem_V6l c4
  obtain ⟨s12, s13, s23, s14, s24, s34⟩ := control_sqd
  have p : ∀ {v v' w w' : V}, v ∈ V6l → v' ∈ V6l → w ∈ V6l → w' ∈ V6l →
      ‖σ (vec v) - vec w‖ ≤ 22 * d → ‖σ (vec v') - vec w'‖ ≤ 22 * d → sqd w w' = sqd v v' :=
    fun hv hv' hw hw' ev ev' =>
      sqd_preserved hd0 hd ev ev' (sqd_corner_le _ hv _ hv') (sqd_corner_le _ hw _ hw')
  obtain ⟨B, hB, hB1, hB2, hB3, hB4⟩ := four_corners w1 m1 w2 m2 w3 m3 w4 m4
    ((p la1 la2 m1 m2 e1 e2).trans s12) ((p la1 la3 m1 m3 e1 e3).trans s13)
    ((p la2 la3 m2 m3 e2 e3).trans s23) ((p la1 la4 m1 m4 e1 e4).trans s14)
    ((p la2 la4 m2 m4 e2 e4).trans s24) ((p la3 la4 m3 m4 e3 e4).trans s34)
  -- the defect `D = σ - B` is affine and small at the four control corners
  obtain ⟨A, hA⟩ := exists_linear σ
  set D : E → E := fun y => σ y - B.toFun y
  have hDc : ∀ k : V, ∀ w : V, B.actV k = w → ‖σ (vec k) - vec w‖ ≤ 22 * d → ‖D (vec k)‖ ≤ 22 * d := by
    intro k w hk hk'; simp only [D]; rw [toFun_vec, hk]; exact hk'
  have D1 := hDc a1 w1 hB1 e1; have D2 := hDc a2 w2 hB2 e2
  have D3 := hDc a3 w3 hB3 e3; have D4 := hDc a4 w4 hB4 e4
  have Dlin : ∀ y z : E, D y - D z = A (y - z) - B.r.lin (y - z) := by
    intro y z; simp only [D, Pose.toFun]; rw [← hA, map_sub]; abel
  have hDgen : ∀ y : E, (∀ i, -1 / 100 ≤ y i ∧ y i ≤ 2 + 1 / 100) → ‖σ y - B.toFun y‖ ≤ 290 * d := by
    intro y hy
    set l2 := (y 1) / 2 - ((y 0 + y 1 + y 2) / 2 - 1)
    set l3 := (y 2) / 2 - ((y 0 + y 1 + y 2) / 2 - 1)
    set l4 := (y 0 + y 1 + y 2) / 2 - 1
    have hDy : D y = D (vec a1) + l2 • (D (vec a2) - D (vec a1)) +
        l3 • (D (vec a3) - D (vec a1)) + l4 • (D (vec a4) - D (vec a1)) := by
      have e := Dlin y (vec a1)
      rw [barycentric y] at e
      simp only [map_add, map_smul] at e
      rw [Dlin, Dlin, Dlin]
      rw [sub_eq_iff_eq_add'] at e
      rw [e]
      simp only [smul_sub]; abel
    obtain ⟨y0l, y0u⟩ := hy 0; obtain ⟨y1l, y1u⟩ := hy 1; obtain ⟨y2l, y2u⟩ := hy 2
    have b2 : |l2| ≤ 203 / 100 := by rw [abs_le]; constructor <;> simp only [l2] <;> linarith
    have b3 : |l3| ≤ 203 / 100 := by rw [abs_le]; constructor <;> simp only [l3] <;> linarith
    have b4 : |l4| ≤ 203 / 100 := by rw [abs_le]; constructor <;> simp only [l4] <;> linarith
    have n2 : ‖D (vec a2) - D (vec a1)‖ ≤ 44 * d := (norm_sub_le _ _).trans (by linarith)
    have n3 : ‖D (vec a3) - D (vec a1)‖ ≤ 44 * d := (norm_sub_le _ _).trans (by linarith)
    have n4 : ‖D (vec a4) - D (vec a1)‖ ≤ 44 * d := (norm_sub_le _ _).trans (by linarith)
    show ‖D y‖ ≤ 290 * d
    rw [hDy]
    calc _ ≤ ‖D (vec a1)‖ + ‖l2 • (D (vec a2) - D (vec a1))‖ + ‖l3 • (D (vec a3) - D (vec a1))‖ +
          ‖l4 • (D (vec a4) - D (vec a1))‖ := norm_add₄_le
      _ ≤ 22 * d + 203 / 100 * (44 * d) + 203 / 100 * (44 * d) + 203 / 100 * (44 * d) := by
          simp only [norm_smul, Real.norm_eq_abs]
          gcongr
      _ ≤ 290 * d := by nlinarith
  have in_box : ∀ {q : E}, q ∈ Q → ∀ i, -1 / 100 ≤ q i ∧ q i ≤ 2 + 1 / 100 := by
    intro q hq i
    obtain ⟨l, u⟩ := Q_bounds hq i
    constructor <;> linarith
  rcases syms_kind B hB with ⟨hr, ht⟩ | hswap | ⟨pr, hpr, hs, ht, hp⟩
  · -- `B` is the identity
    have := hDgen x hx
    have hid : B.toFun x = x := by
      simp only [Pose.toFun, hr, ht, Rot.lin_id]
      simp [vec]
      rfl
    rw [hid] at this
    linarith
  · -- `B` swaps the ends of the diagonal: the origin would land near `(2,2,2)`
    exfalso
    have h0Q : vec 0 ∈ Q := corner_mem 0 (fun i => by simp) ⟨0, by simp⟩
    have hb := hDgen (vec 0) (in_box h0Q)
    rw [toFun_vec, hswap] at hb
    obtain ⟨q, hq, hq1⟩ := hN _ h0Q
    obtain ⟨i, hi⟩ := Q_low hq
    have hfar : 1 - 12 / 10000 ≤ ‖q - vec ![2, 2, 2]‖ := by
      refine le_trans ?_ (abs_apply_le _ i)
      simp only [PiLp.sub_apply, vec_apply]
      have : ((![2, 2, 2] : V) i : ℝ) = 2 := by fin_cases i <;> simp
      rw [this, abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    have := norm_sub_le_norm_sub_add_norm_sub q (σ (vec 0)) (vec ![2, 2, 2])
    rw [norm_sub_rev q (σ (vec 0))] at this
    linarith
  · -- `B` is a non-trivial axis permutation: its probe lands far from `Q`
    exfalso
    set aE : E := WithLp.toLp 2 fun i => sc (pr.apex i)
    have haQ : aE ∈ Q := probe_mem hpr
    have hb := hDgen aE (in_box haQ)
    set tE : E := WithLp.toLp 2 fun i => sc (pr.t i)
    have hBa : B.toFun aE = tE := by
      ext i
      simp only [Pose.toFun, ht, PiLp.add_apply, Rot.lin_apply, hs, hp, vec_apply, aE, tE]
      rw [probes_image pr hpr i]
      fin_cases i <;> simp
    rw [hBa] at hb
    obtain ⟨y, hy, hy1⟩ := hN _ haQ
    obtain ⟨i, hi⟩ := probe_far hpr hy
    have hyt : ‖y - tE‖ ≤ 291 * d := by
      have := norm_sub_le_norm_sub_add_norm_sub y (σ aE) tE
      rw [norm_sub_rev y (σ aE)] at this
      linarith
    have hc : |y i - sc (pr.t i)| ≤ ‖y - tE‖ :=
      calc |y i - sc (pr.t i)| = |(y - tE) i| := rfl
        _ ≤ ‖y - tE‖ := abs_apply_le _ _
    linarith

end
