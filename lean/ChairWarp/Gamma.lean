import Mathlib

/-!
# Chair44's motion group, as integer data

Poses are signed permutations followed by integer translations, acting by
`x ↦ (s i * x (p i))_i + t`, exactly as in the paper's Table 1. We prove:

* `Rot.comp_mem`: the 24 proper signed permutations `R24` are closed under composition.
* `Pose.comp_inGamma`: `Γ = R24 ⋉ BCC` is closed under composition (BCC: all coordinates
  of one parity).
* `level_inGamma`: every tile of every substitution patch (8^n tiles) has its pose in `Γ`.
* `atlas_inGamma`: all 44 legal contacts of the paper's atlas lie in `Γ`.
* `stabilizer_F0`: inside `Γ`, the reference unit face (doubled centre `(1,1,0)`) is fixed only
  by the identity and the diagonal half-turn `(x,y,z) ↦ (y,x,-z)`.
* `face_transitive`: `Γ` carries the reference face onto every unit face of the cubic grid.
-/

abbrev V := Fin 3 → ℤ

/-- A signed permutation: `x ↦ (s i * x (p i))_i`. -/
structure Rot where
  p : Fin 3 → Fin 3
  s : Fin 3 → ℤ

instance : DecidableEq Rot := fun a b =>
  decidable_of_iff (a.p = b.p ∧ a.s = b.s) (by cases a; cases b; simp)

namespace Rot

def act (r : Rot) (x : V) : V := fun i => r.s i * x (r.p i)

/-- `r.comp q` acts as `r ∘ q`. -/
def comp (r q : Rot) : Rot := ⟨fun i => q.p (r.p i), fun i => r.s i * q.s (r.p i)⟩

lemma act_comp (r q : Rot) (x : V) : (r.comp q).act x = r.act (q.act x) := by
  funext i; simp [act, comp, mul_assoc]

def id : Rot := ⟨![0, 1, 2], ![1, 1, 1]⟩

/-- The diagonal half-turn `(x,y,z) ↦ (y,x,-z)`. -/
def sigma : Rot := ⟨![1, 0, 2], ![1, 1, -1]⟩

def perms : List (Fin 3 → Fin 3) :=
  [![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

def permSign (p : Fin 3 → Fin 3) : ℤ :=
  (if p 0 < p 1 then 1 else -1) * (if p 0 < p 2 then 1 else -1) * (if p 1 < p 2 then 1 else -1)

def signVecs : List (Fin 3 → ℤ) :=
  [1, -1].flatMap fun a => [1, -1].flatMap fun b => [1, -1].map fun c => ![a, b, c]

/-- The 24 proper rotations of the cube. -/
def R24 : List Rot :=
  (perms.flatMap fun p => signVecs.map fun s => (⟨p, s⟩ : Rot)).filter
    fun r => permSign r.p * r.s 0 * r.s 1 * r.s 2 = 1

lemma R24_length : R24.length = 24 := by decide

lemma comp_mem : ∀ a ∈ R24, ∀ b ∈ R24, a.comp b ∈ R24 := by decide +kernel

lemma signs_unit : ∀ r ∈ R24, ∀ i, r.s i = 1 ∨ r.s i = -1 := by decide +kernel

end Rot

/-- Body-centred cubic lattice: all coordinates have the same parity. -/
def bcc (t : V) : Prop := 2 ∣ t 0 - t 1 ∧ 2 ∣ t 1 - t 2

instance (t : V) : Decidable (bcc t) := by unfold bcc; infer_instance

lemma bcc_pair {t : V} (h : bcc t) (i j : Fin 3) : 2 ∣ t i - t j := by
  obtain ⟨h1, h2⟩ := h
  fin_cases i <;> fin_cases j <;> simp <;> omega

lemma bcc_add {t u : V} (ht : bcc t) (hu : bcc u) : bcc (t + u) := by
  obtain ⟨a, b⟩ := ht; obtain ⟨c, d⟩ := hu
  constructor <;> simp only [Pi.add_apply] <;> omega

lemma bcc_two_mul (t : V) : bcc (fun i => 2 * t i) :=
  ⟨⟨t 0 - t 1, by ring⟩, ⟨t 1 - t 2, by ring⟩⟩

lemma bcc_act {r : Rot} (hr : r ∈ Rot.R24) {t : V} (ht : bcc t) : bcc (r.act t) := by
  have hs := Rot.signs_unit r hr
  have p01 := bcc_pair ht (r.p 0) (r.p 1)
  have p12 := bcc_pair ht (r.p 1) (r.p 2)
  unfold bcc Rot.act
  generalize t (r.p 0) = a at *; generalize t (r.p 1) = b at *; generalize t (r.p 2) = c at *
  rcases hs 0 with h0 | h0 <;> rcases hs 1 with h1 | h1 <;> rcases hs 2 with h2 | h2 <;>
    simp only [h0, h1, h2] <;> constructor <;> omega

structure Pose where
  r : Rot
  t : V

namespace Pose

/-- `P.comp Q` acts as `P ∘ Q`. -/
def comp (P Q : Pose) : Pose := ⟨P.r.comp Q.r, P.r.act Q.t + P.t⟩

def InGamma (P : Pose) : Prop := P.r ∈ Rot.R24 ∧ bcc P.t

instance (P : Pose) : Decidable P.InGamma := by unfold InGamma; infer_instance

theorem comp_inGamma {P Q : Pose} (hP : P.InGamma) (hQ : Q.InGamma) : (P.comp Q).InGamma :=
  ⟨Rot.comp_mem _ hP.1 _ hQ.1, bcc_add (bcc_act hP.1 hQ.2) hP.2⟩

/-- Refinement of the paper, `(G, t) ↦ (G H, 2 t + G u)` for a child pose `(H, u)`. -/
def refine (P c : Pose) : Pose := ⟨P.r.comp c.r, fun i => P.r.act c.t i + 2 * P.t i⟩

theorem refine_inGamma {P c : Pose} (hP : P.InGamma) (hc : c.InGamma) :
    (P.refine c).InGamma := by
  refine ⟨Rot.comp_mem _ hP.1 _ hc.1, ?_⟩
  have := bcc_add (bcc_act hP.1 hc.2) (bcc_two_mul P.t)
  simpa [Pi.add_def, Pose.refine] using this

end Pose

/-- The eight child poses of the doubled chair (paper, Table 1). -/
def children : List Pose := [
  ⟨⟨![0, 1, 2], ![1, 1, 1]⟩, ![0, 0, 0]⟩,
  ⟨⟨![1, 0, 2], ![1, 1, -1]⟩, ![0, 0, 4]⟩,
  ⟨⟨![0, 2, 1], ![1, -1, 1]⟩, ![0, 4, 0]⟩,
  ⟨⟨![2, 0, 1], ![1, -1, -1]⟩, ![0, 4, 4]⟩,
  ⟨⟨![2, 1, 0], ![-1, 1, 1]⟩, ![4, 0, 0]⟩,
  ⟨⟨![1, 2, 0], ![-1, 1, -1]⟩, ![4, 0, 4]⟩,
  ⟨⟨![0, 1, 2], ![-1, -1, 1]⟩, ![4, 4, 0]⟩,
  ⟨⟨![0, 1, 2], ![1, 1, 1]⟩, ![1, 1, 1]⟩
]

/-- The 44-contact atlas `A44` (paper, Figure 7), recomputed independently. -/
def atlas44 : List Pose := [
    ⟨⟨![2, 0, 1], ![-1, -1, 1]⟩, ![3, 3, 1]⟩,
  ⟨⟨![0, 2, 1], ![1, 1, -1]⟩, ![1, 1, 3]⟩,
  ⟨⟨![1, 2, 0], ![-1, -1, 1]⟩, ![2, 2, 2]⟩,
  ⟨⟨![1, 2, 0], ![1, -1, -1]⟩, ![2, 2, 2]⟩,
  ⟨⟨![0, 2, 1], ![1, -1, 1]⟩, ![-1, 3, -1]⟩,
  ⟨⟨![0, 2, 1], ![-1, 1, 1]⟩, ![4, 0, 0]⟩,
  ⟨⟨![2, 0, 1], ![-1, -1, 1]⟩, ![2, 2, -2]⟩,
  ⟨⟨![0, 1, 2], ![-1, -1, 1]⟩, ![3, 3, 1]⟩,
  ⟨⟨![2, 0, 1], ![-1, 1, -1]⟩, ![2, -2, 2]⟩,
  ⟨⟨![0, 1, 2], ![-1, 1, -1]⟩, ![2, -2, 2]⟩,
  ⟨⟨![2, 0, 1], ![1, -1, -1]⟩, ![-2, 2, 2]⟩,
  ⟨⟨![0, 1, 2], ![1, -1, -1]⟩, ![-2, 2, 2]⟩,
  ⟨⟨![2, 1, 0], ![1, 1, -1]⟩, ![1, 1, 3]⟩,
  ⟨⟨![1, 0, 2], ![1, -1, 1]⟩, ![0, 4, 0]⟩,
  ⟨⟨![2, 1, 0], ![-1, 1, 1]⟩, ![3, -1, -1]⟩,
  ⟨⟨![1, 0, 2], ![1, 1, -1]⟩, ![0, 0, 0]⟩,
  ⟨⟨![2, 0, 1], ![1, -1, -1]⟩, ![-1, 3, 3]⟩,
  ⟨⟨![0, 1, 2], ![-1, 1, -1]⟩, ![2, 2, 2]⟩,
  ⟨⟨![0, 1, 2], ![-1, -1, 1]⟩, ![3, 3, -1]⟩,
  ⟨⟨![1, 0, 2], ![-1, 1, 1]⟩, ![0, 0, 0]⟩,
  ⟨⟨![2, 1, 0], ![-1, 1, 1]⟩, ![4, 0, 0]⟩,
  ⟨⟨![0, 1, 2], ![-1, -1, 1]⟩, ![2, 2, -2]⟩,
  ⟨⟨![1, 2, 0], ![-1, 1, -1]⟩, ![3, -1, 3]⟩,
  ⟨⟨![2, 0, 1], ![1, -1, -1]⟩, ![2, 2, 2]⟩,
  ⟨⟨![1, 2, 0], ![-1, -1, 1]⟩, ![3, 3, 1]⟩,
  ⟨⟨![1, 0, 2], ![1, 1, -1]⟩, ![1, 1, 3]⟩,
  ⟨⟨![0, 1, 2], ![1, 1, 1]⟩, ![-1, -1, -1]⟩,
  ⟨⟨![0, 2, 1], ![1, 1, -1]⟩, ![0, 0, 4]⟩,
  ⟨⟨![0, 1, 2], ![1, 1, 1]⟩, ![1, 1, 1]⟩,
  ⟨⟨![1, 0, 2], ![-1, 1, 1]⟩, ![4, 0, 0]⟩,
  ⟨⟨![1, 2, 0], ![-1, -1, 1]⟩, ![2, 2, -2]⟩,
  ⟨⟨![1, 0, 2], ![1, 1, -1]⟩, ![-1, -1, 3]⟩,
  ⟨⟨![0, 2, 1], ![1, -1, 1]⟩, ![0, 4, 0]⟩,
  ⟨⟨![2, 1, 0], ![1, 1, -1]⟩, ![0, 0, 4]⟩,
  ⟨⟨![2, 0, 1], ![-1, -1, 1]⟩, ![2, 2, 2]⟩,
  ⟨⟨![1, 2, 0], ![-1, 1, -1]⟩, ![2, 2, 2]⟩,
  ⟨⟨![0, 1, 2], ![1, -1, -1]⟩, ![2, 2, 2]⟩,
  ⟨⟨![2, 1, 0], ![1, -1, 1]⟩, ![0, 4, 0]⟩,
  ⟨⟨![1, 0, 2], ![1, 1, -1]⟩, ![0, 0, 4]⟩,
  ⟨⟨![1, 0, 2], ![1, -1, 1]⟩, ![0, 0, 0]⟩,
  ⟨⟨![0, 1, 2], ![-1, -1, 1]⟩, ![2, 2, 2]⟩,
  ⟨⟨![1, 2, 0], ![-1, 1, -1]⟩, ![2, -2, 2]⟩,
  ⟨⟨![1, 2, 0], ![1, -1, -1]⟩, ![-2, 2, 2]⟩,
  ⟨⟨![2, 0, 1], ![-1, 1, -1]⟩, ![2, 2, 2]⟩
]

theorem children_inGamma : ∀ c ∈ children, c.InGamma := by decide +kernel

theorem atlas_inGamma : ∀ c ∈ atlas44, c.InGamma := by decide +kernel

theorem atlas_length : atlas44.length = 44 := by rfl

def level : ℕ → List Pose
  | 0 => [⟨Rot.id, 0⟩]
  | n + 1 => (level n).flatMap fun P => children.map P.refine

theorem level_inGamma : ∀ n, ∀ P ∈ level n, P.InGamma := by
  intro n
  induction n with
  | zero =>
    intro P hP
    simp [level] at hP
    subst hP
    exact ⟨by decide +kernel, by decide⟩
  | succ n ih =>
    intro P hP
    simp only [level, List.mem_flatMap, List.mem_map] at hP
    obtain ⟨Q, hQ, c, hc, rfl⟩ := hP
    exact Pose.refine_inGamma (ih Q hQ) (children_inGamma c hc)

/-! ## Unit faces of the cubic grid

A unit face is recorded by its doubled centre: exactly one coordinate is even. -/

def v0 : V := ![1, 1, 0]

def IsFace (c : V) : Prop :=
  (c 0 % 2 = 0 ∧ c 1 % 2 = 1 ∧ c 2 % 2 = 1) ∨ (c 0 % 2 = 1 ∧ c 1 % 2 = 0 ∧ c 2 % 2 = 1) ∨
    (c 0 % 2 = 1 ∧ c 1 % 2 = 1 ∧ c 2 % 2 = 0)

instance (c : V) : Decidable (IsFace c) := by unfold IsFace; infer_instance

/-- The pose `(r, t)` moves the reference face (doubled centre `v0`) to doubled centre `c`. -/
def Moves (r : Rot) (t : V) (c : V) : Prop := ∀ i, r.act v0 i + 2 * t i = c i

/-- Decidable criterion: some `t ∈ BCC` realises `Moves r t c`. -/
def Reach (r : Rot) (c : V) : Prop :=
  (∀ i, 2 ∣ c i - r.act v0 i) ∧ 4 ∣ (c 0 - r.act v0 0) - (c 1 - r.act v0 1) ∧
    4 ∣ (c 1 - r.act v0 1) - (c 2 - r.act v0 2)

instance (r : Rot) (c : V) : Decidable (Reach r c) := by unfold Reach; infer_instance

lemma reach_iff (r : Rot) (c : V) : Reach r c ↔ ∃ t, bcc t ∧ Moves r t c := by
  unfold Reach Moves bcc
  generalize r.act v0 = w
  constructor
  · rintro ⟨h, h01, h12⟩
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    refine ⟨fun i => (c i - w i) / 2, ⟨?_, ?_⟩, ?_⟩
    · simp only; omega
    · simp only; omega
    · intro i
      have hi := h i
      simp only; omega
  · rintro ⟨t, ⟨a, b⟩, hm⟩
    have m0 := hm 0; have m1 := hm 1; have m2 := hm 2
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have := hm i; omega
    · omega
    · omega

/-- `Reach r c` only depends on `c` modulo 4. -/
lemma reach_mod (r : Rot) (c : V) : Reach r c ↔ Reach r (fun i => c i % 4) := by
  unfold Reach
  generalize r.act v0 = w
  constructor
  · rintro ⟨h, h01, h12⟩
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have := h i; simp only; omega
    · simp only; omega
    · simp only; omega
  · rintro ⟨h, h01, h12⟩
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have := h i; simp only at this; omega
    · simp only at h01; omega
    · simp only at h12; omega

/-- Finite check over residues modulo 4. -/
lemma face_transitive_mod4 :
    ∀ ρ : Fin 3 → Fin 4, IsFace (fun i => (ρ i : ℤ)) →
      ∃ r ∈ Rot.R24, Reach r (fun i => (ρ i : ℤ)) := by
  decide +kernel

theorem face_transitive (c : V) (hc : IsFace c) :
    ∃ r ∈ Rot.R24, ∃ t, bcc t ∧ Moves r t c := by
  let ρ : Fin 3 → Fin 4 := fun i => ⟨(c i % 4).toNat, by omega⟩
  have hρ : (fun i => (ρ i : ℤ)) = fun i => c i % 4 := by
    funext i; simp only [ρ]; omega
  have hface : IsFace (fun i => (ρ i : ℤ)) := by
    rw [hρ]; unfold IsFace at hc ⊢; simp only; omega
  obtain ⟨r, hr, hreach⟩ := face_transitive_mod4 ρ hface
  rw [hρ, ← reach_mod, reach_iff] at hreach
  exact ⟨r, hr, hreach⟩

/-- Rotation criterion for fixing the reference face. -/
lemma stabilizer_rot :
    ∀ r ∈ Rot.R24, Reach r v0 ↔ (r = Rot.id ∨ r = Rot.sigma) := by
  decide +kernel

theorem stabilizer_F0 (r : Rot) (hr : r ∈ Rot.R24) :
    (∃ t, bcc t ∧ Moves r t v0) ↔ (r = Rot.id ∨ r = Rot.sigma) := by
  rw [← reach_iff]; exact stabilizer_rot r hr

/-- In the stabilizer the translation is forced to be zero. -/
theorem stabilizer_translation {r : Rot} (hr : r = Rot.id ∨ r = Rot.sigma) {t : V}
    (h : Moves r t v0) : t = 0 := by
  funext i
  have := h i
  rcases hr with rfl | rfl <;> fin_cases i <;> simp_all [Moves, Rot.act, Rot.id, Rot.sigma, v0]
