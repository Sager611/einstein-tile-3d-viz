import ChairWarp.Geometry

/-!
# Chair44 as a concrete subset of ℝ³

`Q` is the paper's solid (arXiv 2609.19214, §2): the seven-cube carrier `P` with 192 square-pyramid
features. Feature `f` sits on the panel with outward normal `f.sg • e_{f.ax}`, base centre `f.c`
(units of 1/10000), base half-width `η = 1/100` and signed height `f.a / 10000`; near it the solid is
the hypograph of the tent `z ≤ h · (1 - ‖u‖∞ / η)`. Bumps (`a > 0`) add the tent above the panel;
dents (`a < 0`) remove it below.

Every point of `Q` lies in one of 103 integer boxes (7 cubes, 96 bump boxes). All geometric facts
used by the rigidity argument are then decided on these boxes.
-/

structure Feat where
  ax : Fin 3
  sg : ℤ
  c : Fin 3 → ℤ
  a : ℤ

/-- The 192 features, independently transcribed from the paper's pinned solid data. -/
def feats : List Feat := [
    ⟨0, -1, ![0, 2500, 3750], 5⟩,
  ⟨0, -1, ![0, 2500, 6250], 6⟩,
  ⟨0, -1, ![0, 3750, 2500], 1⟩,
  ⟨0, -1, ![0, 3750, 7500], 2⟩,
  ⟨0, -1, ![0, 6250, 2500], 3⟩,
  ⟨0, -1, ![0, 6250, 7500], 4⟩,
  ⟨0, -1, ![0, 7500, 3750], 7⟩,
  ⟨0, -1, ![0, 7500, 6250], 8⟩,
  ⟨0, -1, ![0, 2500, 13750], -6⟩,
  ⟨0, -1, ![0, 2500, 16250], -5⟩,
  ⟨0, -1, ![0, 3750, 12500], -2⟩,
  ⟨0, -1, ![0, 3750, 17500], -1⟩,
  ⟨0, -1, ![0, 6250, 12500], -4⟩,
  ⟨0, -1, ![0, 6250, 17500], -3⟩,
  ⟨0, -1, ![0, 7500, 13750], -8⟩,
  ⟨0, -1, ![0, 7500, 16250], -7⟩,
  ⟨0, -1, ![0, 12500, 3750], 2⟩,
  ⟨0, -1, ![0, 12500, 6250], 4⟩,
  ⟨0, -1, ![0, 13750, 2500], 6⟩,
  ⟨0, -1, ![0, 13750, 7500], 8⟩,
  ⟨0, -1, ![0, 16250, 2500], 5⟩,
  ⟨0, -1, ![0, 16250, 7500], 7⟩,
  ⟨0, -1, ![0, 17500, 3750], 1⟩,
  ⟨0, -1, ![0, 17500, 6250], 3⟩,
  ⟨0, -1, ![0, 12500, 13750], -9⟩,
  ⟨0, -1, ![0, 12500, 16250], -11⟩,
  ⟨0, -1, ![0, 13750, 12500], 9⟩,
  ⟨0, -1, ![0, 13750, 17500], 10⟩,
  ⟨0, -1, ![0, 16250, 12500], 11⟩,
  ⟨0, -1, ![0, 16250, 17500], 12⟩,
  ⟨0, -1, ![0, 17500, 13750], -10⟩,
  ⟨0, -1, ![0, 17500, 16250], -12⟩,
  ⟨0, 1, ![10000, 12500, 13750], -5⟩,
  ⟨0, 1, ![10000, 12500, 16250], -6⟩,
  ⟨0, 1, ![10000, 13750, 12500], -1⟩,
  ⟨0, 1, ![10000, 13750, 17500], -2⟩,
  ⟨0, 1, ![10000, 16250, 12500], -3⟩,
  ⟨0, 1, ![10000, 16250, 17500], -4⟩,
  ⟨0, 1, ![10000, 17500, 13750], -7⟩,
  ⟨0, 1, ![10000, 17500, 16250], -8⟩,
  ⟨0, 1, ![20000, 2500, 3750], 12⟩,
  ⟨0, 1, ![20000, 2500, 6250], 10⟩,
  ⟨0, 1, ![20000, 3750, 2500], -12⟩,
  ⟨0, 1, ![20000, 3750, 7500], -11⟩,
  ⟨0, 1, ![20000, 6250, 2500], -10⟩,
  ⟨0, 1, ![20000, 6250, 7500], -9⟩,
  ⟨0, 1, ![20000, 7500, 3750], 11⟩,
  ⟨0, 1, ![20000, 7500, 6250], 9⟩,
  ⟨0, 1, ![20000, 2500, 13750], -3⟩,
  ⟨0, 1, ![20000, 2500, 16250], -1⟩,
  ⟨0, 1, ![20000, 3750, 12500], -7⟩,
  ⟨0, 1, ![20000, 3750, 17500], -5⟩,
  ⟨0, 1, ![20000, 6250, 12500], -8⟩,
  ⟨0, 1, ![20000, 6250, 17500], -6⟩,
  ⟨0, 1, ![20000, 7500, 13750], -4⟩,
  ⟨0, 1, ![20000, 7500, 16250], -2⟩,
  ⟨0, 1, ![20000, 12500, 3750], 7⟩,
  ⟨0, 1, ![20000, 12500, 6250], 8⟩,
  ⟨0, 1, ![20000, 13750, 2500], 3⟩,
  ⟨0, 1, ![20000, 13750, 7500], 4⟩,
  ⟨0, 1, ![20000, 16250, 2500], 1⟩,
  ⟨0, 1, ![20000, 16250, 7500], 2⟩,
  ⟨0, 1, ![20000, 17500, 3750], 5⟩,
  ⟨0, 1, ![20000, 17500, 6250], 6⟩,
  ⟨1, -1, ![2500, 0, 3750], -5⟩,
  ⟨1, -1, ![2500, 0, 6250], -6⟩,
  ⟨1, -1, ![3750, 0, 2500], -1⟩,
  ⟨1, -1, ![3750, 0, 7500], -2⟩,
  ⟨1, -1, ![6250, 0, 2500], -3⟩,
  ⟨1, -1, ![6250, 0, 7500], -4⟩,
  ⟨1, -1, ![7500, 0, 3750], -7⟩,
  ⟨1, -1, ![7500, 0, 6250], -8⟩,
  ⟨1, -1, ![2500, 0, 13750], 6⟩,
  ⟨1, -1, ![2500, 0, 16250], 5⟩,
  ⟨1, -1, ![3750, 0, 12500], 2⟩,
  ⟨1, -1, ![3750, 0, 17500], 1⟩,
  ⟨1, -1, ![6250, 0, 12500], 4⟩,
  ⟨1, -1, ![6250, 0, 17500], 3⟩,
  ⟨1, -1, ![7500, 0, 13750], 8⟩,
  ⟨1, -1, ![7500, 0, 16250], 7⟩,
  ⟨1, 1, ![2500, 20000, 3750], -12⟩,
  ⟨1, 1, ![2500, 20000, 6250], -10⟩,
  ⟨1, 1, ![3750, 20000, 2500], 12⟩,
  ⟨1, 1, ![3750, 20000, 7500], 11⟩,
  ⟨1, 1, ![6250, 20000, 2500], 10⟩,
  ⟨1, 1, ![6250, 20000, 7500], 9⟩,
  ⟨1, 1, ![7500, 20000, 3750], -11⟩,
  ⟨1, 1, ![7500, 20000, 6250], -9⟩,
  ⟨1, 1, ![2500, 20000, 13750], 3⟩,
  ⟨1, 1, ![2500, 20000, 16250], 1⟩,
  ⟨1, 1, ![3750, 20000, 12500], 7⟩,
  ⟨1, 1, ![3750, 20000, 17500], 5⟩,
  ⟨1, 1, ![6250, 20000, 12500], 8⟩,
  ⟨1, 1, ![6250, 20000, 17500], 6⟩,
  ⟨1, 1, ![7500, 20000, 13750], 4⟩,
  ⟨1, 1, ![7500, 20000, 16250], 2⟩,
  ⟨1, -1, ![12500, 0, 3750], -2⟩,
  ⟨1, -1, ![12500, 0, 6250], -4⟩,
  ⟨1, -1, ![13750, 0, 2500], -6⟩,
  ⟨1, -1, ![13750, 0, 7500], -8⟩,
  ⟨1, -1, ![16250, 0, 2500], -5⟩,
  ⟨1, -1, ![16250, 0, 7500], -7⟩,
  ⟨1, -1, ![17500, 0, 3750], -1⟩,
  ⟨1, -1, ![17500, 0, 6250], -3⟩,
  ⟨1, -1, ![12500, 0, 13750], 9⟩,
  ⟨1, -1, ![12500, 0, 16250], 11⟩,
  ⟨1, -1, ![13750, 0, 12500], -9⟩,
  ⟨1, -1, ![13750, 0, 17500], -10⟩,
  ⟨1, -1, ![16250, 0, 12500], -11⟩,
  ⟨1, -1, ![16250, 0, 17500], -12⟩,
  ⟨1, -1, ![17500, 0, 13750], 10⟩,
  ⟨1, -1, ![17500, 0, 16250], 12⟩,
  ⟨1, 1, ![12500, 10000, 13750], 5⟩,
  ⟨1, 1, ![12500, 10000, 16250], 6⟩,
  ⟨1, 1, ![13750, 10000, 12500], 1⟩,
  ⟨1, 1, ![13750, 10000, 17500], 2⟩,
  ⟨1, 1, ![16250, 10000, 12500], 3⟩,
  ⟨1, 1, ![16250, 10000, 17500], 4⟩,
  ⟨1, 1, ![17500, 10000, 13750], 7⟩,
  ⟨1, 1, ![17500, 10000, 16250], 8⟩,
  ⟨1, 1, ![12500, 20000, 3750], -7⟩,
  ⟨1, 1, ![12500, 20000, 6250], -8⟩,
  ⟨1, 1, ![13750, 20000, 2500], -3⟩,
  ⟨1, 1, ![13750, 20000, 7500], -4⟩,
  ⟨1, 1, ![16250, 20000, 2500], -1⟩,
  ⟨1, 1, ![16250, 20000, 7500], -2⟩,
  ⟨1, 1, ![17500, 20000, 3750], -5⟩,
  ⟨1, 1, ![17500, 20000, 6250], -6⟩,
  ⟨2, -1, ![2500, 3750, 0], -12⟩,
  ⟨2, -1, ![2500, 6250, 0], -10⟩,
  ⟨2, -1, ![3750, 2500, 0], 12⟩,
  ⟨2, -1, ![3750, 7500, 0], 11⟩,
  ⟨2, -1, ![6250, 2500, 0], 10⟩,
  ⟨2, -1, ![6250, 7500, 0], 9⟩,
  ⟨2, -1, ![7500, 3750, 0], -11⟩,
  ⟨2, -1, ![7500, 6250, 0], -9⟩,
  ⟨2, 1, ![2500, 3750, 20000], 12⟩,
  ⟨2, 1, ![2500, 6250, 20000], 10⟩,
  ⟨2, 1, ![3750, 2500, 20000], -12⟩,
  ⟨2, 1, ![3750, 7500, 20000], -11⟩,
  ⟨2, 1, ![6250, 2500, 20000], -10⟩,
  ⟨2, 1, ![6250, 7500, 20000], -9⟩,
  ⟨2, 1, ![7500, 3750, 20000], 11⟩,
  ⟨2, 1, ![7500, 6250, 20000], 9⟩,
  ⟨2, -1, ![2500, 13750, 0], -6⟩,
  ⟨2, -1, ![2500, 16250, 0], -5⟩,
  ⟨2, -1, ![3750, 12500, 0], -2⟩,
  ⟨2, -1, ![3750, 17500, 0], -1⟩,
  ⟨2, -1, ![6250, 12500, 0], -4⟩,
  ⟨2, -1, ![6250, 17500, 0], -3⟩,
  ⟨2, -1, ![7500, 13750, 0], -8⟩,
  ⟨2, -1, ![7500, 16250, 0], -7⟩,
  ⟨2, 1, ![2500, 13750, 20000], -3⟩,
  ⟨2, 1, ![2500, 16250, 20000], -1⟩,
  ⟨2, 1, ![3750, 12500, 20000], -7⟩,
  ⟨2, 1, ![3750, 17500, 20000], -5⟩,
  ⟨2, 1, ![6250, 12500, 20000], -8⟩,
  ⟨2, 1, ![6250, 17500, 20000], -6⟩,
  ⟨2, 1, ![7500, 13750, 20000], -4⟩,
  ⟨2, 1, ![7500, 16250, 20000], -2⟩,
  ⟨2, -1, ![12500, 3750, 0], 2⟩,
  ⟨2, -1, ![12500, 6250, 0], 4⟩,
  ⟨2, -1, ![13750, 2500, 0], 6⟩,
  ⟨2, -1, ![13750, 7500, 0], 8⟩,
  ⟨2, -1, ![16250, 2500, 0], 5⟩,
  ⟨2, -1, ![16250, 7500, 0], 7⟩,
  ⟨2, -1, ![17500, 3750, 0], 1⟩,
  ⟨2, -1, ![17500, 6250, 0], 3⟩,
  ⟨2, 1, ![12500, 3750, 20000], 7⟩,
  ⟨2, 1, ![12500, 6250, 20000], 8⟩,
  ⟨2, 1, ![13750, 2500, 20000], 3⟩,
  ⟨2, 1, ![13750, 7500, 20000], 4⟩,
  ⟨2, 1, ![16250, 2500, 20000], 1⟩,
  ⟨2, 1, ![16250, 7500, 20000], 2⟩,
  ⟨2, 1, ![17500, 3750, 20000], 5⟩,
  ⟨2, 1, ![17500, 6250, 20000], 6⟩,
  ⟨2, -1, ![12500, 13750, 0], -9⟩,
  ⟨2, -1, ![12500, 16250, 0], -11⟩,
  ⟨2, -1, ![13750, 12500, 0], 9⟩,
  ⟨2, -1, ![13750, 17500, 0], 10⟩,
  ⟨2, -1, ![16250, 12500, 0], 11⟩,
  ⟨2, -1, ![16250, 17500, 0], 12⟩,
  ⟨2, -1, ![17500, 13750, 0], -10⟩,
  ⟨2, -1, ![17500, 16250, 0], -12⟩,
  ⟨2, 1, ![12500, 13750, 10000], 12⟩,
  ⟨2, 1, ![12500, 16250, 10000], 10⟩,
  ⟨2, 1, ![13750, 12500, 10000], -12⟩,
  ⟨2, 1, ![13750, 17500, 10000], -11⟩,
  ⟨2, 1, ![16250, 12500, 10000], -10⟩,
  ⟨2, 1, ![16250, 17500, 10000], -9⟩,
  ⟨2, 1, ![17500, 13750, 10000], 11⟩,
  ⟨2, 1, ![17500, 16250, 10000], 9⟩
]

def cells : List (Fin 3 → ℤ) :=
  [![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 1, 0]]

lemma feats_length : feats.length = 192 := by rfl

noncomputable section

def η : ℝ := 1 / 100

def sc (z : ℤ) : ℝ := (z : ℝ) / 10000

def inCube (a : Fin 3 → ℤ) (x : E) : Prop := ∀ i, (a i : ℝ) ≤ x i ∧ x i ≤ a i + 1

/-- The seven-cube carrier. -/
def P : Set E := {x | ∃ a ∈ cells, inCube a x}

def uu (f : Feat) (x : E) (j : Fin 3) : ℝ := x j - sc (f.c j)

def ww (f : Feat) (x : E) : ℝ := f.sg * (x f.ax - sc (f.c f.ax))

def bumpSet (f : Feat) : Set E :=
  {x | 0 ≤ ww f x ∧ ∀ j, j ≠ f.ax → |uu f x j| ≤ η ∧ ww f x ≤ sc f.a * (1 - |uu f x j| / η)}

def dentSet (f : Feat) : Set E :=
  {x | ww f x ≤ 0 ∧ ∀ j, j ≠ f.ax → |uu f x j| < η ∧ -(sc (-f.a)) * (1 - |uu f x j| / η) < ww f x}

/-- **Chair44.** -/
def Q : Set E :=
  {x | (x ∈ P ∧ ∀ f ∈ feats, f.a < 0 → x ∉ dentSet f) ∨ ∃ f ∈ feats, 0 < f.a ∧ x ∈ bumpSet f}

end

/-! ## The box cover -/

abbrev Box := Fin 3 → ℤ × ℤ

def cellBox (a : Fin 3 → ℤ) : Box := fun i => (10000 * a i, 10000 * a i + 10000)

def featBox (f : Feat) : Box := fun i =>
  if i = f.ax then (if f.sg = 1 then (f.c i, f.c i + f.a) else (f.c i - f.a, f.c i))
  else (f.c i - 100, f.c i + 100)

def boxes : List Box := cells.map cellBox ++ (feats.filter fun f => decide (0 < f.a)).map featBox

def InBox (b : Box) (x : E) : Prop := ∀ i, ((b i).1 : ℝ) ≤ 10000 * x i ∧ 10000 * x i ≤ (b i).2

lemma feats_sg : ∀ f ∈ feats, f.sg = 1 ∨ f.sg = -1 := by decide +kernel

lemma P_sub {x : E} (hx : x ∈ P) : ∃ b ∈ boxes, InBox b x := by
  obtain ⟨a, ha, hc⟩ := hx
  refine ⟨cellBox a, List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩), fun i => ?_⟩
  obtain ⟨h1, h2⟩ := hc i
  simp only [cellBox]; push_cast
  constructor <;> linarith

lemma bump_sub {f : Feat} (hf : f ∈ feats) (hpos : 0 < f.a) {x : E} (hx : x ∈ bumpSet f) :
    InBox (featBox f) x := by
  obtain ⟨hw0, hj⟩ := hx
  -- some in-plane index exists
  obtain ⟨j0, hj0⟩ : ∃ j, j ≠ f.ax := ⟨f.ax + 1, by simp⟩
  obtain ⟨hu0, hw1⟩ := hj j0 hj0
  have hη : (0 : ℝ) < η := by norm_num [η]
  have hfac : 1 - |uu f x j0| / η ≤ 1 := by
    have : 0 ≤ |uu f x j0| / η := div_nonneg (abs_nonneg _) hη.le
    linarith
  have hsa : 0 ≤ sc f.a := by unfold sc; positivity
  have hwa : ww f x ≤ sc f.a := by nlinarith
  intro i
  by_cases hi : i = f.ax
  · subst hi
    simp only [featBox, if_pos rfl]
    rcases feats_sg f hf with hs | hs
    · simp only [hs, if_true]
      simp only [ww, hs, Int.cast_one, one_mul, sc] at hw0 hwa
      push_cast; constructor <;> nlinarith
    · simp only [hs, show (-1 : ℤ) ≠ 1 by decide, if_false]
      simp only [ww, hs, Int.cast_neg, Int.cast_one, sc] at hw0 hwa
      push_cast; constructor <;> nlinarith
  · simp only [featBox, if_neg hi]
    have hu := (hj i hi).1
    simp only [uu, sc, η] at hu
    rw [abs_le] at hu
    push_cast; constructor <;> nlinarith

lemma Q_sub {x : E} (hx : x ∈ Q) : ∃ b ∈ boxes, InBox b x := by
  rcases hx with ⟨hP, _⟩ | ⟨f, hf, hpos, hb⟩
  · exact P_sub hP
  · refine ⟨featBox f, List.mem_append_right _ (List.mem_map.mpr ⟨f, ?_, rfl⟩),
      bump_sub hf hpos hb⟩
    exact List.mem_filter.mpr ⟨hf, by simpa using hpos⟩

/-! ## Decided box facts -/

lemma boxes_bounds : ∀ b ∈ boxes, ∀ i, -12 ≤ (b i).1 ∧ (b i).2 ≤ 20012 := by decide +kernel

lemma boxes_strip : ∀ b ∈ boxes,
    (∀ i, 0 ≤ (b i).1 ∧ (b i).2 ≤ 20000) ∨ ∃ i, ∀ j, j ≠ i → 2400 ≤ (b j).1 ∧ (b j).2 ≤ 17600 := by
  decide +kernel

lemma boxes_low : ∀ b ∈ boxes, ∃ i, (b i).2 ≤ 10012 := by decide +kernel

/-! ## Real consequences -/

lemma Q_bounds {x : E} (hx : x ∈ Q) (i : Fin 3) : -12 / 10000 ≤ x i ∧ x i ≤ 2 + 12 / 10000 := by
  obtain ⟨b, hb, hin⟩ := Q_sub hx
  obtain ⟨l, u⟩ := boxes_bounds b hb i
  obtain ⟨h1, h2⟩ := hin i
  have l' : (-12 : ℝ) ≤ (b i).1 := by exact_mod_cast l
  have u' : ((b i).2 : ℝ) ≤ 20012 := by exact_mod_cast u
  constructor <;> linarith

lemma Q_strip {x : E} (hx : x ∈ Q) :
    (∀ i, 0 ≤ x i ∧ x i ≤ 2) ∨ ∃ i, ∀ j, j ≠ i → 24 / 100 ≤ x j ∧ x j ≤ 176 / 100 := by
  obtain ⟨b, hb, hin⟩ := Q_sub hx
  rcases boxes_strip b hb with h | ⟨i, h⟩
  · left; intro i
    obtain ⟨l, u⟩ := h i; obtain ⟨h1, h2⟩ := hin i
    have l' : (0 : ℝ) ≤ (b i).1 := by exact_mod_cast l
    have u' : ((b i).2 : ℝ) ≤ 20000 := by exact_mod_cast u
    constructor <;> linarith
  · right; refine ⟨i, fun j hj => ?_⟩
    obtain ⟨l, u⟩ := h j hj; obtain ⟨h1, h2⟩ := hin j
    have l' : (2400 : ℝ) ≤ (b j).1 := by exact_mod_cast l
    have u' : ((b j).2 : ℝ) ≤ 17600 := by exact_mod_cast u
    constructor <;> linarith

lemma Q_low {x : E} (hx : x ∈ Q) : ∃ i, x i ≤ 1 + 12 / 10000 := by
  obtain ⟨b, hb, hin⟩ := Q_sub hx
  obtain ⟨i, h⟩ := boxes_low b hb
  refine ⟨i, ?_⟩
  obtain ⟨_, h2⟩ := hin i
  have u' : ((b i).2 : ℝ) ≤ 10012 := by exact_mod_cast h
  linarith

/-! ## Corners lie in `Q` -/

lemma corner_cell : ∀ k : Fin 3 → Fin 3, (∀ i, k i ≠ 1) → (∃ i, k i = 0) →
    ∃ a ∈ cells, ∀ i, a i ≤ 2 * (k i : ℤ) / 2 ∧ 2 * (k i : ℤ) / 2 ≤ a i + 1 := by
  decide +kernel

lemma feats_center : ∀ f ∈ feats, ∀ j, j ≠ f.ax → 2400 ≤ f.c j ∧ f.c j ≤ 17600 := by
  decide +kernel

/-- A box corner (coordinates in `{0, 2}`) other than `(2,2,2)` lies in `Q`. -/
lemma corner_mem (v : V) (hv : ∀ i, v i = 0 ∨ v i = 2) (hne : ∃ i, v i = 0) : vec v ∈ Q := by
  left
  refine ⟨?_, fun f hf _ hd => ?_⟩
  · -- the cell below the corner
    let a : Fin 3 → ℤ := fun i => if v i = 0 then 0 else 1
    have ha : a ∈ cells := by
      obtain ⟨i, hi⟩ := hne
      have h0 : a 0 = 0 ∨ a 0 = 1 := by simp only [a]; split_ifs <;> simp
      have h1 : a 1 = 0 ∨ a 1 = 1 := by simp only [a]; split_ifs <;> simp
      have h2 : a 2 = 0 ∨ a 2 = 1 := by simp only [a]; split_ifs <;> simp
      have hai : a i = 0 := by simp [a, hi]
      have : a = ![a 0, a 1, a 2] := by funext j; fin_cases j <;> rfl
      rw [this]
      fin_cases i <;> simp at hai <;>
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
        simp_all [cells]
    refine ⟨a, ha, fun i => ?_⟩
    simp only [vec_apply, a]
    rcases hv i with h | h <;> simp [h] <;> norm_num
  · obtain ⟨j0, hj0⟩ : ∃ j, j ≠ f.ax := ⟨f.ax + 1, by simp⟩
    have hu := (hd.2 j0 hj0).1
    obtain ⟨l, u⟩ := feats_center f hf j0 hj0
    simp only [uu, sc, η, vec_apply] at hu
    rw [abs_lt] at hu
    have l' : (2400 : ℝ) ≤ f.c j0 := by exact_mod_cast l
    have u' : (f.c j0 : ℝ) ≤ 17600 := by exact_mod_cast u
    rcases hv j0 with h | h <;> rw [h] at hu <;> push_cast at hu <;>
      obtain ⟨h1, h2⟩ := hu <;> nlinarith

/-! ## Probes -/

structure Probe where
  p : Fin 3 → Fin 3
  apex : Fin 3 → ℤ
  t : Fin 3 → ℤ

/-- For each non-identity permutation of the axes: a height-12 bump apex whose permuted image lies
above a dent. -/
def probes : List Probe := [
  ⟨![0, 2, 1], ![-12, 16250, 17500], ![-12, 17500, 16250]⟩,
  ⟨![1, 0, 2], ![-12, 16250, 17500], ![16250, -12, 17500]⟩,
  ⟨![1, 2, 0], ![3750, 2500, -12], ![2500, -12, 3750]⟩,
  ⟨![2, 0, 1], ![12500, 13750, 10012], ![10012, 12500, 13750]⟩,
  ⟨![2, 1, 0], ![-12, 16250, 17500], ![17500, 16250, -12]⟩
]

/-- Probe apexes are apexes of bumps of `Q`. -/
lemma probes_apex : ∀ pr ∈ probes, ∃ f ∈ feats, 0 < f.a ∧
    (∀ j, j ≠ f.ax → pr.apex j = f.c j) ∧ pr.apex f.ax = f.c f.ax + f.sg * f.a := by
  decide +kernel

lemma probes_image : ∀ pr ∈ probes, ∀ i, pr.t i = pr.apex (pr.p i) := by decide +kernel

lemma probes_sep : ∀ pr ∈ probes, ∀ b ∈ boxes, ∃ i, (b i).2 + 1 ≤ pr.t i ∨ pr.t i ≤ (b i).1 - 1 := by
  decide +kernel

/-- The probe apex lies in `Q`. -/
lemma probe_mem {pr : Probe} (hpr : pr ∈ probes) :
    (WithLp.toLp 2 fun i => sc (pr.apex i) : E) ∈ Q := by
  obtain ⟨f, hf, hpos, hin, hax⟩ := probes_apex pr hpr
  right
  refine ⟨f, hf, hpos, ?_, fun j hj => ?_⟩
  · simp only [ww, sc, hax]
    have ha : (0 : ℝ) < f.a := by exact_mod_cast hpos
    rcases feats_sg f hf with hs | hs <;> rw [hs] <;> push_cast <;> nlinarith
  · simp only [uu, hin j hj, sub_self, abs_zero, zero_div, sub_zero, mul_one, ww, hax, sc]
    refine ⟨by norm_num [η], ?_⟩
    rcases feats_sg f hf with hs | hs <;> simp [hs] <;> push_cast <;> ring_nf <;> nlinarith

/-- The permuted probe image is at least `1/10000` (in some coordinate) from every point of `Q`. -/
lemma probe_far {pr : Probe} (hpr : pr ∈ probes) {y : E} (hy : y ∈ Q) :
    ∃ i, 1 / 10000 ≤ |y i - sc (pr.t i)| := by
  obtain ⟨b, hb, hin⟩ := Q_sub hy
  obtain ⟨i, h⟩ := probes_sep pr hpr b hb
  refine ⟨i, ?_⟩
  obtain ⟨h1, h2⟩ := hin i
  simp only [sc]
  rcases h with h | h
  · have h' : ((b i).2 : ℝ) + 1 ≤ pr.t i := by exact_mod_cast h
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · have h' : (pr.t i : ℝ) ≤ (b i).1 - 1 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith
