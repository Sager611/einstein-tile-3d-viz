import ChairWarp.Tile

/-!
# Near-diametral pairs of Chair44 sit at opposite box corners

If two points of `Q` are almost `√12` apart, both are within `κ/2` (coordinatewise) of opposite
corners of the `2 × 2 × 2` box, and neither corner is `(0,0,0)` or `(2,2,2)`.
-/

lemma norm_sq_three (x : E) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

lemma norm_le_sum_abs (x : E) : ‖x‖ ≤ |x 0| + |x 1| + |x 2| := by
  have h := norm_sq_three x
  have hn := norm_nonneg x
  have hs : 0 ≤ |x 0| + |x 1| + |x 2| := by positivity
  nlinarith [sq_abs (x 0), sq_abs (x 1), sq_abs (x 2), abs_nonneg (x 0), abs_nonneg (x 1),
    abs_nonneg (x 2), mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1)),
    mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 2)), mul_nonneg (abs_nonneg (x 1)) (abs_nonneg (x 2))]

lemma abs_apply_le (x : E) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i

/-- A corner of the box other than `(0,0,0)` and `(2,2,2)`. -/
def IsCorner6 (w : V) : Prop := (∀ i, w i = 0 ∨ w i = 2) ∧ (∃ i, w i = 0) ∧ ∃ i, w i = 2

/-- Coordinatewise facts in the box case. -/
lemma pair_coord {a b κ : ℝ} (ha : 0 ≤ a ∧ a ≤ 2) (hb : 0 ≤ b ∧ b ≤ 2) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 1) (h : 4 - κ ≤ (a - b) ^ 2) :
    (a ≤ κ / 2 ∧ 2 - κ / 2 ≤ b) ∨ (2 - κ / 2 ≤ a ∧ b ≤ κ / 2) := by
  rcases le_total a b with hab | hab
  · left; constructor <;> nlinarith
  · right; constructor <;> nlinarith

theorem near_diametral {q q' : E} (hq : q ∈ Q) (hq' : q' ∈ Q) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 1 / 1000) (hd : 12 - κ ≤ ‖q - q'‖ ^ 2) :
    ∃ w : V, IsCorner6 w ∧ ∀ i, |q i - w i| ≤ κ / 2 := by
  rw [norm_sq_three] at hd
  simp only [PiLp.sub_apply] at hd
  have bq := Q_bounds hq; have bq' := Q_bounds hq'
  -- rule out the strip cases
  have far_sq : ∀ {x y : E}, x ∈ Q → y ∈ Q → ∀ j, (x j - y j) ^ 2 ≤ (20024 / 10000) ^ 2 := by
    intro x y hx hy j
    obtain ⟨a1, a2⟩ := Q_bounds hx j; obtain ⟨b1, b2⟩ := Q_bounds hy j
    exact sq_le_sq' (by linarith) (by linarith)
  have mid_sq : ∀ {x y : E}, y ∈ Q → ∀ j, 24 / 100 ≤ x j ∧ x j ≤ 176 / 100 →
      (x j - y j) ^ 2 ≤ (17612 / 10000) ^ 2 := by
    intro x y hy j ⟨l, u⟩
    obtain ⟨b1, b2⟩ := Q_bounds hy j
    exact sq_le_sq' (by linarith) (by linarith)
  have strip_false : ∀ {x y : E}, x ∈ Q → y ∈ Q →
      (∃ i, ∀ j, j ≠ i → 24 / 100 ≤ x j ∧ x j ≤ 176 / 100) →
      (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 < 12 - κ := by
    intro x y hx hy ⟨i, hi⟩
    have f0 := far_sq hx hy 0; have f1 := far_sq hx hy 1; have f2 := far_sq hx hy 2
    fin_cases i
    · have m1 := mid_sq hy 1 (hi 1 (by decide)); have m2 := mid_sq hy 2 (hi 2 (by decide))
      norm_num at f0 m1 m2 ⊢; linarith
    · have m0 := mid_sq hy 0 (hi 0 (by decide)); have m2 := mid_sq hy 2 (hi 2 (by decide))
      norm_num at f1 m0 m2 ⊢; linarith
    · have m0 := mid_sq hy 0 (hi 0 (by decide)); have m1 := mid_sq hy 1 (hi 1 (by decide))
      norm_num at f2 m0 m1 ⊢; linarith
  rcases Q_strip hq with box | s
  swap
  · exact absurd hd (not_le.mpr (strip_false hq hq' s))
  rcases Q_strip hq' with box' | s'
  swap
  · have := strip_false hq' hq s'
    have e : (q' 0 - q 0) ^ 2 + (q' 1 - q 1) ^ 2 + (q' 2 - q 2) ^ 2 =
        (q 0 - q' 0) ^ 2 + (q 1 - q' 1) ^ 2 + (q 2 - q' 2) ^ 2 := by ring
    exact absurd hd (not_le.mpr (by linarith))
  have cq : ∀ i, (q i ≤ κ / 2 ∧ 2 - κ / 2 ≤ q' i) ∨ (2 - κ / 2 ≤ q i ∧ q' i ≤ κ / 2) := by
    intro i
    apply pair_coord (box i) (box' i) hκ0 (by linarith)
    have in4 : ∀ j, (q j - q' j) ^ 2 ≤ 4 := fun j => by
      obtain ⟨a1, a2⟩ := box j; obtain ⟨b1, b2⟩ := box' j
      nlinarith
    have s0 := in4 0; have s1 := in4 1; have s2 := in4 2
    fin_cases i <;> simp <;> linarith
  let w : V := fun i => if q i ≤ 1 then 0 else 2
  have hw : ∀ i, |q i - w i| ≤ κ / 2 := by
    intro i
    simp only [w]
    rcases cq i with ⟨h1, _⟩ | ⟨h1, _⟩
    · have hle : q i ≤ 1 := by linarith
      rw [if_pos hle]; push_cast; rw [abs_le]; constructor <;> linarith [(box i).1]
    · have hgt : ¬ q i ≤ 1 := by linarith
      rw [if_neg hgt]; push_cast; rw [abs_le]; constructor <;> linarith [(box i).2]
  refine ⟨w, ⟨fun i => by simp only [w]; split_ifs <;> simp, ?_, ?_⟩, hw⟩
  · obtain ⟨i, hi⟩ := Q_low hq
    refine ⟨i, ?_⟩
    rcases cq i with ⟨h1, _⟩ | ⟨h1, _⟩
    · simp only [w]; rw [if_pos (by linarith)]
    · exfalso; linarith
  · obtain ⟨i, hi⟩ := Q_low hq'
    refine ⟨i, ?_⟩
    rcases cq i with ⟨_, h2⟩ | ⟨h1, _⟩
    · exfalso; linarith
    · simp only [w]; rw [if_neg (by linarith)]
