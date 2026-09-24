import ChairWarp.Warp

/-!
# Equivariant warps cannot resize Chair44's arms

Every map that commutes with Chair44's motion group fixes every point of the integer grid. In
particular all corners of the seven carrier cubes stay put: a `Γ`-equivariant warp can bend faces and
edges, but it cannot lengthen, shorten, thicken or thin any arm.

Proof: the half-turns `H₁ = diag(1,-1,-1)` and `H₂ = diag(-1,1,-1)`, followed by the translations
`v - Hᵢ v` (all coordinates even, so in the body-centred lattice), lie in `Γ` and fix the grid point
`v`. Equivariance makes the displacement `Φ v - v` fixed by both half-turns, hence zero.
-/

def H1 : Rot := ⟨![0, 1, 2], ![1, -1, -1]⟩
def H2 : Rot := ⟨![0, 1, 2], ![-1, 1, -1]⟩

lemma H1_mem : H1 ∈ Rot.R24 := by decide +kernel
lemma H2_mem : H2 ∈ Rot.R24 := by decide +kernel

/-- The motion `x ↦ H x + (v - H v)`, which fixes `v`. -/
def fixPose (H : Rot) (v : V) : Pose := ⟨H, fun i => v i - H.act v i⟩

lemma fixPose1_inGamma (v : V) : (fixPose H1 v).InGamma := by
  refine ⟨H1_mem, ?_, ?_⟩ <;> simp [fixPose, H1, Rot.act] <;> omega

lemma fixPose2_inGamma (v : V) : (fixPose H2 v).InGamma := by
  refine ⟨H2_mem, ?_, ?_⟩ <;> simp [fixPose, H2, Rot.act] <;> omega

lemma fixPose_toFun (H : Rot) (v : V) (x : E) :
    (fixPose H v).toFun x = H.lin x + (vec v - H.lin (vec v)) := by
  ext i; simp [fixPose, Pose.toFun, Rot.act]

/-- **Obstruction.** Every `Γ`-equivariant map fixes every point of the integer grid. -/
theorem equivariant_fixes_grid (Φ : E → E)
    (hΦ : ∀ γ ∈ GammaGeom, ∀ x, Φ (γ x) = γ (Φ x)) (v : V) : Φ (vec v) = vec v := by
  have key : ∀ H : Rot, ∀ hP : (fixPose H v).InGamma,
      H.lin (Φ (vec v) - vec v) = Φ (vec v) - vec v := by
    intro H hP
    have h := hΦ _ (toIso_mem _ hP) (vec v)
    simp only [Pose.toIso_apply, fixPose_toFun] at h
    have hv : H.lin (vec v) + (vec v - H.lin (vec v)) = vec v := by abel
    rw [hv] at h
    rw [map_sub]
    calc H.lin (Φ (vec v)) - H.lin (vec v)
        = (H.lin (Φ (vec v)) + (vec v - H.lin (vec v))) - vec v := by abel
      _ = Φ (vec v) - vec v := by rw [← h]
  have k1 := key H1 (fixPose1_inGamma v)
  have k2 := key H2 (fixPose2_inGamma v)
  set d := Φ (vec v) - vec v
  have c1 := congrArg (fun z : E => z 1) k1
  have c2 := congrArg (fun z : E => z 2) k1
  have c0 := congrArg (fun z : E => z 0) k2
  simp [H1, H2] at c0 c1 c2
  have hd : d = 0 := by
    ext i; fin_cases i <;> simp <;> linarith
  exact sub_eq_zero.mp hd

/-- In particular the proved warp leaves every corner of every tile where it was. -/
theorem warp_fixes_grid (v : V) : warp (vec v) = vec v :=
  equivariant_fixes_grid warp warp_comm v
