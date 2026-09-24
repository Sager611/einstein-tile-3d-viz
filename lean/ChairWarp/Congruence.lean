import ChairWarp.FamilyFinal
import ChairWarp.Obstruction

/-!
# Different amplitudes give non-congruent tiles

1. `congr_eq_one`: if an isometry `σ` carries one warped Chair44 onto another (any two certified-small
   waves and amplitudes), then `σ = 1`. `σ` is a near-symmetry of Chair44, hence close to the identity
   on the box (`near_id_on_box`). Equivariant warps fix grid points (`equivariant_fixes_grid`), and
   near each of four convex corners of Chair44 every warped tile lies in a narrow cone around an
   octant. A near-identity isometry that maps one such cone-shaped corner into another must fix the
   corner, and an isometry fixing `0, 2e₀, 2e₁, 2e₂` is the identity.
2. `image_strictMono`: for `s < t` the certificate point of the `t`-tile lies outside the `s`-tile.

Hence `family_noncongruent`: within each certified family, distinct amplitudes give non-congruent
solids, so each family `A`, `B`, `C` contains infinitely many pairwise non-congruent tiles.
-/

open Set Real

namespace WaveSpec

/-! ## Corner data (all `decide`) -/

/-- Four convex corners of Chair44 with the sign pattern of their octant. -/
def corners : List (V × V) :=
  [(![0, 0, 0], ![1, 1, 1]), (![2, 0, 0], ![-1, 1, 1]), (![0, 2, 0], ![1, -1, 1]),
    (![0, 0, 2], ![1, 1, -1])]

lemma corners_boxes : ∀ p ∈ corners, ∀ b ∈ boxes,
    (∃ i, (b i).2 ≤ 10000 * p.1 i - 1000 ∨ 10000 * p.1 i + 1000 ≤ (b i).1) ∨
    (∀ i, (p.2 i = 1 ∧ 10000 * p.1 i ≤ (b i).1) ∨ (p.2 i = -1 ∧ (b i).2 ≤ 10000 * p.1 i)) := by
  decide +kernel

lemma corners_sign : ∀ p ∈ corners, ∀ i, p.2 i = 1 ∨ p.2 i = -1 := by decide +kernel

lemma corners_range : ∀ p ∈ corners, ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ 2 := by decide +kernel

lemma corners_cells : ∀ p ∈ corners, ∃ a ∈ cells, ∀ i, a i ≤ p.1 i ∧ p.1 i ≤ a i + 1 := by
  decide +kernel

lemma corners_notDent : ∀ p ∈ corners, ∀ f ∈ feats, f.a < 0 →
    ∃ j, j ≠ f.ax ∧ 100 ≤ |10000 * p.1 j - f.c j| := by
  decide +kernel

lemma corner_mem {p : V × V} (hp : p ∈ corners) : vec p.1 ∈ Q := by
  left
  obtain ⟨a, ha, hin⟩ := corners_cells p hp
  refine ⟨⟨a, ha, fun i => ?_⟩, fun f hf hneg hd => ?_⟩
  · obtain ⟨h1, h2⟩ := hin i
    simp only [vec_apply]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · obtain ⟨j, hj, hsep⟩ := corners_notDent p hp f hf hneg
    have hu := (hd.2 j hj).1
    simp only [uu, sc, η, vec_apply] at hu
    rw [abs_lt] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hs : (100 : ℝ) ≤ |((10000 * p.1 j - f.c j : ℤ) : ℝ)| := by exact_mod_cast hsep
    push_cast at hs
    rcases le_abs'.mp hs with h | h <;> linarith

/-! ## Cones at corners -/

def nd (n : V) (y : E) : ℝ := n 0 * y 0 + n 1 * y 1 + n 2 * y 2

lemma nd_add (n : V) (y z : E) : nd n (y + z) = nd n y + nd n z := by simp [nd]; ring

lemma nd_neg_sub (n : V) (y c : E) : nd n (c - y) = - nd n (y - c) := by simp [nd]; ring

lemma abs_sign_mul {m : ℤ} (h : m = 1 ∨ m = -1) (y : ℝ) : |(m : ℝ) * y| = |y| := by
  rcases h with rfl | rfl <;> simp

lemma nd_upper {n : V} (hn : ∀ i, n i = 1 ∨ n i = -1) (y : E) : nd n y ≤ 3 * ‖y‖ := by
  have h : ∀ i, (n i : ℝ) * y i ≤ ‖y‖ := fun i =>
    (le_abs_self _).trans ((abs_sign_mul (hn i) _).le.trans (abs_apply_le y i))
  unfold nd; linarith [h 0, h 1, h 2]

lemma nd_lower {n : V} (hn : ∀ i, n i = 1 ∨ n i = -1) (y : E) (hy : ∀ i, 0 ≤ (n i : ℝ) * y i) :
    ‖y‖ ≤ nd n y := by
  have h : ∀ i, (n i : ℝ) * y i = |y i| := fun i => by
    rw [← abs_sign_mul (hn i) (y i), abs_of_nonneg (hy i)]
  refine (norm_le_abs_sum y).trans ?_
  unfold nd; rw [h 0, h 1, h 2]

lemma octant {p : V × V} (hp : p ∈ corners) {q : E} (hq : q ∈ Q) (hn : ‖q - vec p.1‖ < 1 / 10)
    (i : Fin 3) : 0 ≤ (p.2 i : ℝ) * (q - vec p.1) i := by
  obtain ⟨b, hb, hin⟩ := Q_sub hq
  have near : ∀ j, |q j - p.1 j| < 1 / 10 := fun j => by
    have := (abs_apply_le (q - vec p.1) j).trans_lt hn
    simpa [vec_apply] using this
  rcases corners_boxes p hp b hb with ⟨j, hj | hj⟩ | hall
  · exfalso
    have c1 : ((b j).2 : ℝ) ≤ 10000 * p.1 j - 1000 := by exact_mod_cast hj
    have := (hin j).2
    have := abs_lt.mp (near j)
    linarith
  · exfalso
    have c1 : (10000 * p.1 j + 1000 : ℝ) ≤ (b j).1 := by exact_mod_cast hj
    have := (hin j).1
    have := abs_lt.mp (near j)
    linarith
  · simp only [PiLp.sub_apply, vec_apply]
    rcases hall i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]
      have c : (10000 * p.1 i : ℝ) ≤ (b i).1 := by exact_mod_cast h2
      have := (hin i).1
      push_cast; linarith
    · rw [h1]
      have c : ((b i).2 : ℝ) ≤ 10000 * p.1 i := by exact_mod_cast h2
      have := (hin i).2
      push_cast; linarith

variable {w : WaveSpec} (hw : w.Good) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10 ^ 9)

/-- Near a corner, every point of the warped tile lies in a cone around the corner's octant. -/
lemma cone {p : V × V} (hp : p ∈ corners) {q : E} (hq : q ∈ Q) (hn : ‖q - vec p.1‖ < 1 / 10) :
    ‖w.warp hw s hs0 hs q - vec p.1‖ ≤ 3 * nd p.2 (w.warp hw s hs0 hs q - vec p.1) := by
  set c := vec p.1
  have hfix : w.warp hw s hs0 hs c = c := equivariant_fixes_grid _ (w.warp_comm hw s hs0 hs) _
  rw [warp_apply, warpFun] at hfix
  have hf0 : w.field s c = 0 := by
    have := congrArg (fun z => z - c) hfix; simpa using this
  set y := q - c
  set z := w.field s q - w.field s c
  have he : w.warp hw s hs0 hs q - c = y + z := by
    rw [warp_apply, warpFun]; simp only [y, z, hf0]; abel
  have hz : ‖z‖ ≤ 1 / 5 * ‖y‖ := w.field_lipschitz hw hs0 hs q c
  have hsg := corners_sign p hp
  have hy : ‖y‖ ≤ nd p.2 y := nd_lower hsg y (octant hp hq hn)
  have hzl : -(3 * ‖z‖) ≤ nd p.2 z := by
    have := nd_upper hsg (-z)
    simp only [nd, PiLp.neg_apply, norm_neg] at this ⊢; linarith
  rw [he, nd_add]
  have := norm_add_le y z
  linarith

/-! ## Rigidity between two warped tiles -/

lemma nearSym₂ {w' : WaveSpec} (hw' : w'.Good) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 10 ^ 9)
    {σ : E ≃ᵢ E} (h : σ '' (w.warp hw s hs0 hs '' Q) = w'.warp hw' t ht0 ht '' Q) :
    NearSym (48 * s + 48 * t) σ := by
  intro q hq
  have hmem : σ (w.warp hw s hs0 hs q) ∈ w'.warp hw' t ht0 ht '' Q :=
    h ▸ mem_image_of_mem σ (mem_image_of_mem _ hq)
  obtain ⟨q', hq', hq'e⟩ := hmem
  refine ⟨q', hq', ?_⟩
  have h1 : ‖σ q - σ (w.warp hw s hs0 hs q)‖ ≤ 48 * s := by
    rw [← dist_eq_norm, σ.dist_eq, dist_eq_norm, norm_sub_rev]
    exact w.norm_warp_sub_le hw s hs0 hs q
  have h2 : ‖w'.warp hw' t ht0 ht q' - q'‖ ≤ 48 * t := w'.norm_warp_sub_le hw' t ht0 ht q'
  calc ‖σ q - q'‖ = ‖(σ q - σ (w.warp hw s hs0 hs q)) + (w'.warp hw' t ht0 ht q' - q')‖ := by
        rw [hq'e]; congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ 48 * s + 48 * t := by linarith

/-- **No congruences.** An isometry between two small certified warps of Chair44 is the identity. -/
theorem congr_eq_one {w' : WaveSpec} (hw' : w'.Good) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 10 ^ 9)
    (σ : E ≃ᵢ E) (h : σ '' (w.warp hw s hs0 hs '' Q) = w'.warp hw' t ht0 ht '' Q) : σ = 1 := by
  set d := 48 * s + 48 * t
  have hd0 : 0 ≤ d := by positivity
  have hd7 : d ≤ 1 / 10 ^ 7 := by simp only [d]; linarith [show (96 : ℝ) / 10 ^ 9 ≤ 1 / 10 ^ 7 by norm_num]
  set δ := 300 * d
  have hδ : δ ≤ 3 / 10 ^ 5 := by simp only [δ]; linarith [show (300 : ℝ) / 10 ^ 7 ≤ 3 / 10 ^ 5 by norm_num]
  have hδ0 : 0 ≤ δ := by positivity
  have hnear : ∀ x : E, (∀ i, -1 / 100 ≤ x i ∧ x i ≤ 2 + 1 / 100) → ‖σ x - x‖ ≤ δ :=
    fun x hx => near_id_on_box hd0 hd7 (nearSym₂ hw hs0 hs hw' ht0 ht h) x hx
  -- linear part (Mazur–Ulam)
  let τ : E ≃ᵢ E := σ.trans (IsometryEquiv.addRight (-σ 0))
  have hτ0 : τ 0 = 0 := by simp [τ]
  let Aℓ := τ.toRealLinearIsometryEquivOfMapZero hτ0
  have hA : ∀ x, Aℓ x = σ x - σ 0 := fun x => by simp [Aℓ, τ, sub_eq_add_neg]
  have hdiff : ∀ x y, σ x - σ y = Aℓ (x - y) := fun x y => by rw [map_sub, hA, hA]; abel
  set c0 : E := vec ![1, 1, 1]
  have hunit : ∀ u : E, ‖u‖ ≤ 1 → ‖Aℓ u - u‖ ≤ 2 * δ := by
    intro u hu
    have hb : ∀ v : E, ‖v‖ ≤ 1 → ∀ i, -1 / 100 ≤ (c0 + v) i ∧ (c0 + v) i ≤ 2 + 1 / 100 := by
      intro v hv i
      have := (abs_apply_le v i).trans hv
      have h1 : ((![1, 1, 1] : V) i : ℝ) = 1 := by fin_cases i <;> simp
      simp only [c0, PiLp.add_apply, vec_apply, h1]
      rw [abs_le] at this; constructor <;> linarith [this.1, this.2]
    have h1 := hnear (c0 + u) (hb u hu)
    have h2 := hnear c0 (by simpa using hb 0 (by simp))
    have e : Aℓ u - u = (σ (c0 + u) - (c0 + u)) - (σ c0 - c0) := by
      rw [← add_sub_cancel_left c0 u, ← hdiff]; abel
    rw [e]
    calc _ ≤ ‖σ (c0 + u) - (c0 + u)‖ + ‖σ c0 - c0‖ := norm_sub_le _ _
      _ ≤ 2 * δ := by linarith
  have hall : ∀ v : E, ‖Aℓ v - v‖ ≤ 2 * δ * ‖v‖ := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      set u := ‖v‖⁻¹ • v
      have hu : ‖u‖ ≤ 1 := by simp [u, norm_smul, inv_mul_cancel₀ hn.ne']
      have hvu : v = ‖v‖ • u := by simp [u, smul_smul, mul_inv_cancel₀ hn.ne']
      have e : Aℓ v - v = ‖v‖ • (Aℓ u - u) := by
        conv_lhs => rw [hvu]
        rw [map_smul, smul_sub]
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hn]
      nlinarith [hunit u hu]
  -- every listed corner is fixed
  have hcorner : ∀ p ∈ corners, σ (vec p.1) = vec p.1 := by
    intro p hp
    set c := vec p.1
    have hsg := corners_sign p hp
    have hcQ := corner_mem hp
    have hcbox : ∀ i, -1 / 100 ≤ c i ∧ c i ≤ 2 + 1 / 100 := fun i => by
      obtain ⟨a, b⟩ := corners_range p hp i
      have a' : (0 : ℝ) ≤ p.1 i := by exact_mod_cast a
      have b' : (p.1 i : ℝ) ≤ 2 := by exact_mod_cast b
      simp only [c, vec_apply]; constructor <;> linarith
    have hσc := hnear c hcbox
    have hWc : w.warp hw s hs0 hs c = c := equivariant_fixes_grid _ (w.warp_comm hw s hs0 hs) _
    have hW'c : w'.warp hw' t ht0 ht c = c := equivariant_fixes_grid _ (w'.warp_comm hw' t ht0 ht) _
    -- `σ c` lies in the cone of the target tile
    obtain ⟨q', hq', hq'e⟩ : σ c ∈ w'.warp hw' t ht0 ht '' Q :=
      h ▸ mem_image_of_mem σ ⟨c, hcQ, hWc⟩
    have hq'n : ‖q' - c‖ < 1 / 10 := by
      have := w'.norm_warp_sub_le hw' t ht0 ht q'
      rw [hq'e] at this
      calc ‖q' - c‖ = ‖(σ c - c) - (σ c - q')‖ := by congr 1; abel
        _ ≤ ‖σ c - c‖ + ‖σ c - q'‖ := norm_sub_le _ _
        _ < 1 / 10 := by linarith
    have cone1 := cone hw' ht0 ht hp hq' hq'n
    rw [hq'e] at cone1
    -- `y = σ⁻¹ c` lies in the cone of the source tile
    obtain ⟨y, hyA, hyc⟩ : c ∈ σ '' (w.warp hw s hs0 hs '' Q) := h ▸ ⟨c, hcQ, hW'c⟩
    obtain ⟨q'', hq'', hq''e⟩ := hyA
    have hyn : ‖y - c‖ ≤ δ := by
      rw [← dist_eq_norm, ← σ.dist_eq, hyc, dist_eq_norm, norm_sub_rev]; exact hσc
    have hq''n : ‖q'' - c‖ < 1 / 10 := by
      have := w.norm_warp_sub_le hw s hs0 hs q''
      rw [hq''e] at this
      calc ‖q'' - c‖ = ‖(y - c) - (y - q'')‖ := by congr 1; abel
        _ ≤ ‖y - c‖ + ‖y - q''‖ := norm_sub_le _ _
        _ < 1 / 10 := by linarith
    have cone2 := cone hw hs0 hs hp hq'' hq''n
    rw [hq''e] at cone2
    -- combine: `σ c - c = A (c - y)`
    set v := c - y
    have hv : σ c - c = Aℓ v := by have := hdiff c y; rw [hyc] at this; exact this
    have hsplit : nd p.2 (Aℓ v) = nd p.2 v + nd p.2 (Aℓ v - v) := by
      rw [← nd_add]; congr 1; abel
    have hup := nd_upper hsg (Aℓ v - v)
    have hvn : ‖v‖ = ‖y - c‖ := by rw [norm_sub_rev]
    have hneg : nd p.2 v = - nd p.2 (y - c) := nd_neg_sub _ _ _
    have hpos : 0 ≤ nd p.2 (σ c - c) := by
      have := norm_nonneg (σ c - c); linarith
    rw [hv] at hpos
    have hvz : ‖v‖ = 0 := by
      have := hall v
      have := norm_nonneg v
      nlinarith
    have hv0 : v = 0 := norm_eq_zero.mp hvz
    have : y = c := by have := sub_eq_zero.mp hv0; exact this.symm
    calc σ c = σ y := by rw [this]
      _ = c := hyc
  -- an isometry fixing `0, 2e₀, 2e₁, 2e₂` is the identity
  have f0 := hcorner (![0, 0, 0], ![1, 1, 1]) (by simp [corners])
  have f1 := hcorner (![2, 0, 0], ![-1, 1, 1]) (by simp [corners])
  have f2 := hcorner (![0, 2, 0], ![1, -1, 1]) (by simp [corners])
  have f3 := hcorner (![0, 0, 2], ![1, 1, -1]) (by simp [corners])
  simp only at f0 f1 f2 f3
  have hz : vec ![0, 0, 0] = (0 : E) := by ext i; fin_cases i <;> simp
  rw [hz] at f0
  have hAx : ∀ x, Aℓ x = σ x := fun x => by rw [hA, f0, sub_zero]
  ext x : 1
  have hx : x = (x 0 / 2) • vec ![2, 0, 0] + (x 1 / 2) • vec ![0, 2, 0] + (x 2 / 2) • vec ![0, 0, 2] := by
    ext i; fin_cases i <;> simp <;> ring
  rw [← hAx, hx, map_add, map_add, map_smul, map_smul, map_smul, hAx, hAx, hAx, f1, f2, f3]
  rfl

/-! ## Distinct amplitudes give distinct solids -/

lemma field_smul_one (s : ℝ) (x : E) : w.field s x = s • w.field 1 x := by
  simp [field, smul_smul]

include hw in
lemma field_one_lip (x y : E) : ‖w.field 1 x - w.field 1 y‖ ≤ 384 * π * ‖x - y‖ := by
  unfold field
  rw [one_smul, one_smul, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ R ∈ Rot.S24, ‖w.wave (R.lin x) • R.inv.lin (vec w.e) -
        w.wave (R.lin y) • R.inv.lin (vec w.e)‖ := norm_sum_le _ _
    _ ≤ Rot.S24.card • (16 * π * ‖x - y‖) :=
        Finset.sum_le_card_nsmul _ _ _ fun R hR => w.norm_term_sub hw (Rot.mem_S24.mp hR) x y
    _ = 384 * π * ‖x - y‖ := by rw [Rot.S24_card]; simp; ring

/-- For `s < t`, the certificate point of the `t`-tile is not in the `s`-tile. -/
theorem image_strictMono {P8 : V} (hc : w.Cert P8) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 10 ^ 9)
    (hst : s < t) : w.warp hw t ht0 ht (pt P8) ∉ w.warp hw s hs0 hs '' Q := by
  rintro ⟨q, hq, he⟩
  set x := pt P8
  set u := q - x
  have hV1 := field_one_lip hw q x
  have hV : ‖w.field 1 x‖ ≤ 48 := by simpa using w.norm_field_le hw zero_le_one x
  rw [warp_apply, warp_apply, warpFun, warpFun, w.field_smul_one s, w.field_smul_one t] at he
  have hu : u = (t - s) • w.field 1 x - s • (w.field 1 q - w.field 1 x) := by
    have hq' : q = x + t • w.field 1 x - s • w.field 1 q := by rw [← he]; abel
    simp only [u]; rw [sub_smul, smul_sub]; nth_rewrite 1 [hq']; abel
  have hπ := Real.pi_le_four
  have hts : 0 < t - s := by linarith
  have hsL : s * (384 * π) ≤ 1 / 1000 := by
    have : s * (384 * π) ≤ (1 / 10 ^ 9) * (384 * 4) :=
      mul_le_mul hs (by linarith) (by positivity) (by norm_num)
    linarith [show (1 / 10 ^ 9 : ℝ) * (384 * 4) ≤ 1 / 1000 by norm_num]
  have herr : ‖s • (w.field 1 q - w.field 1 x)‖ ≤ s * (384 * π) * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    calc s * ‖w.field 1 q - w.field 1 x‖ ≤ s * (384 * π * ‖u‖) := by gcongr
      _ = _ := by ring
  have hun : ‖u‖ ≤ 49 * (t - s) := by
    have h1 : ‖u‖ ≤ (t - s) * 48 + s * (384 * π) * ‖u‖ := by
      calc ‖u‖ ≤ ‖(t - s) • w.field 1 x‖ + ‖s • (w.field 1 q - w.field 1 x)‖ := by
            rw [hu]; exact norm_sub_le _ _
        _ ≤ (t - s) * 48 + s * (384 * π) * ‖u‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hts]; gcongr
    have := norm_nonneg u
    nlinarith
  have herr' : ‖s • (w.field 1 q - w.field 1 x)‖ ≤ (t - s) / 20 := by
    have := norm_nonneg u
    nlinarith
  -- coordinates of `u`
  have hcoord : ∀ i, |u i - (t - s) * w.field 1 x i| ≤ (t - s) / 20 := by
    intro i
    have := (abs_apply_le (s • (w.field 1 q - w.field 1 x)) i).trans herr'
    rw [hu]; simpa [abs_sub_comm] using this
  have fx : ∀ i, w.field 1 x i = ((∑ R ∈ Rot.S24, cosA (w.qR P8 R) * w.cR R i : ℤ) : ℝ) := by
    intro i; rw [show x = pt P8 from rfl]; unfold pt; rw [w.field_eighth 1 P8 hc.even hc.sqrt2 i, one_mul]
  have hA2 : ((∑ R ∈ Rot.S24, cosA (w.qR P8 R) * w.cR R 2 : ℤ) : ℝ) ≤ -1 := by
    have := hc.f2; exact_mod_cast (show _ ≤ (-1 : ℤ) by omega)
  have u0 := hcoord 0; have u1 := hcoord 1; have u2 := hcoord 2
  rw [fx, hc.f0, Int.cast_zero, mul_zero, sub_zero] at u0
  rw [fx, hc.f1, Int.cast_zero, mul_zero, sub_zero] at u1
  rw [fx] at u2
  have hqi : ∀ i, q i = x i + u i := fun i => by simp [u]
  obtain ⟨b, hb, hin⟩ := Q_sub hq
  obtain ⟨l0, r0⟩ := hin 0; obtain ⟨l1, r1⟩ := hin 1; obtain ⟨l2, r2⟩ := hin 2
  rw [hqi 0, pt_apply] at l0 r0; rw [hqi 1, pt_apply] at l1 r1; rw [hqi 2, pt_apply, hc.z0] at l2 r2
  rw [abs_le] at u0 u1 u2
  have tiny : t - s ≤ 1 / 10 ^ 9 := by linarith
  rcases hc.outside b hb with h | h | h | h | h
  · have : (0 : ℝ) ≤ (b 2).1 := by exact_mod_cast h
    simp only [Int.cast_zero, zero_div, zero_add] at l2
    nlinarith
  · have : ((1250 * P8 0 : ℤ) : ℝ) + 1 ≤ (b 0).1 := by exact_mod_cast h
    push_cast at this; linarith
  · have : ((b 0).2 : ℝ) + 1 ≤ ((1250 * P8 0 : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  · have : ((1250 * P8 1 : ℤ) : ℝ) + 1 ≤ (b 1).1 := by exact_mod_cast h
    push_cast at this; linarith
  · have : ((b 1).2 : ℝ) + 1 ≤ ((1250 * P8 1 : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith

/-- **Non-congruence.** Within a certified family, different amplitudes `s ≠ t` in `[0, 10⁻⁹]` give
solids that are not congruent (and `s = 0` is Chair44 itself). -/
theorem family_noncongruent {P8 : V} (hc : w.Cert P8) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 10 ^ 9)
    (hst : s ≠ t) (σ : E ≃ᵢ E) : σ '' (w.warp hw s hs0 hs '' Q) ≠ w.warp hw t ht0 ht '' Q := by
  intro h
  have h1 := congr_eq_one hw hs0 hs hw ht0 ht σ h
  subst h1
  simp only [IsometryEquiv.coe_one, image_id] at h
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · exact image_strictMono hw hs0 hs hc ht0 ht hlt (h ▸ mem_image_of_mem _ (pt_mem hc))
  · exact image_strictMono hw ht0 ht hc hs0 hs hgt (h.symm ▸ mem_image_of_mem _ (pt_mem hc))

end WaveSpec

/-- **Families A, B, C are infinite**: distinct amplitudes in `(0, 10⁻⁹]` give non-congruent tiles. -/
theorem familyA_noncongruent {s t : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10 ^ 9) (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 10 ^ 9) (hst : s ≠ t) (σ : E ≃ᵢ E) :
    σ '' (famA.warp famA_good s hs0 hs '' Q) ≠ famA.warp famA_good t ht0 ht '' Q :=
  WaveSpec.family_noncongruent famA_good hs0 hs famA_cert ht0 ht hst σ

theorem familyB_noncongruent {s t : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10 ^ 9) (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 10 ^ 9) (hst : s ≠ t) (σ : E ≃ᵢ E) :
    σ '' (famB.warp famB_good s hs0 hs '' Q) ≠ famB.warp famB_good t ht0 ht '' Q :=
  WaveSpec.family_noncongruent famB_good hs0 hs famB_cert ht0 ht hst σ

theorem familyC_noncongruent {s t : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10 ^ 9) (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 10 ^ 9) (hst : s ≠ t) (σ : E ≃ᵢ E) :
    σ '' (famC.warp famC_good s hs0 hs '' Q) ≠ famC.warp famC_good t ht0 ht '' Q :=
  WaveSpec.family_noncongruent famC_good hs0 hs famC_cert ht0 ht hst σ
