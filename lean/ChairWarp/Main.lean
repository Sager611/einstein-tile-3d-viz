import ChairWarp.Transfer
import ChairWarp.Warp

/-!
# Warped Chair44 tilings

Hypotheses are exactly the inputs taken from the paper (arXiv 2609.19214, Theorem 1.2):
the tiling `T = (g i '' Q)` by Chair44 `Q` is registered (neighbouring tiles differ by contacts of the
atlas `A44`, whose poses we proved lie in `Γ`) and has no nonzero translational symmetry.
-/

open Set

/-- Translation by a vector, as an isometry. -/
noncomputable def transl (v : E) : E ≃ᵢ E := IsometryEquiv.addRight v

@[simp] lemma transl_apply (v x : E) : transl v x = x + v := rfl

/-- Lattice translations belong to Chair44's motion group. -/
lemma transl_mem {b : V} (hb : bcc b) : transl (vec b) ∈ GammaGeom := by
  have hid : Rot.id ∈ Rot.R24 := by decide +kernel
  have hP : (⟨Rot.id, b⟩ : Pose).InGamma := ⟨hid, hb⟩
  convert toIso_mem _ hP using 1
  ext x : 1
  simp [Pose.toFun, Rot.lin_id]

variable {ι : Type*}

/-- Symmetries inside `Γ` transfer in both directions, with no rigidity assumption. -/
theorem symm_gamma_iff (Q : Set E) (g : ι → (E ≃ᵢ E)) (hg : ∀ i, g i ∈ GammaGeom)
    {τ : E ≃ᵢ E} (hτ : τ ∈ GammaGeom) :
    IsSymmetry (warp '' Q) g τ ↔ IsSymmetry Q g τ := by
  have comm : ∀ γ ∈ GammaGeom, ∀ S : Set E, γ '' (warp '' S) = warp '' (γ '' S) :=
    fun γ hγ S => image_warp_comm GammaGeom warp warp_comm hγ S
  have key : ∀ i j, τ '' (g i '' (warp '' Q)) = g j '' (warp '' Q) ↔ τ '' (g i '' Q) = g j '' Q := by
    intro i j
    rw [comm _ (hg i), comm _ hτ, comm _ (hg j)]
    exact (image_injective.mpr warp.injective).eq_iff
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => (h1 i).imp fun j => (key i j).mp, fun j => (h2 j).imp fun i => (key i j).mp⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => (h1 i).imp fun j => (key i j).mpr, fun j => (h2 j).imp fun i => (key i j).mpr⟩

/-- Registration glue: if neighbouring tiles differ by motions of `Γ` and every tile is connected
to a root tile placed by the identity, every placement lies in `Γ`. -/
theorem placements_mem (g : ι → (E ≃ᵢ E)) (Adj : ι → ι → Prop)
    (hadj : ∀ i j, Adj i j → (g i)⁻¹ * g j ∈ GammaGeom) (i₀ : ι) (hroot : g i₀ = 1)
    (hconn : ∀ i, Relation.ReflTransGen Adj i₀ i) : ∀ i, g i ∈ GammaGeom := by
  intro i
  induction hconn i with
  | refl => rw [hroot]; exact GammaGeom.one_mem
  | tail _ hab ih =>
    rename_i a b _
    have := GammaGeom.mul_mem ih (hadj a b hab)
    simpa using this

/-- Rigidity reduction: a rigid `Q` has a rigid warp, provided the warp's self-isometries lie in
`Γ`. -/
theorem warp_rigid_of (Q : Set E) (hQ : ∀ σ : E ≃ᵢ E, σ '' Q = Q → σ = 1)
    (hsym : ∀ σ : E ≃ᵢ E, σ '' (warp '' Q) = warp '' Q → σ ∈ GammaGeom) :
    ∀ σ : E ≃ᵢ E, σ '' (warp '' Q) = warp '' Q → σ = 1 := by
  intro σ hσ
  apply hQ σ
  have := hσ
  rw [image_warp_comm GammaGeom warp warp_comm (hsym σ hσ)] at this
  exact (image_injective.mpr warp.injective) this

/-- **Main theorem.** Warping any registered, non-periodic Chair44 tiling by the explicit
`Γ`-equivariant homeomorphism `warp` (which is not the identity) gives
1. a tiling of `ℝ³` by congruent copies of the single solid `warp '' Q`;
2. with no nonzero translational period in the lattice of `Γ` (unconditionally);
3. with no nonzero translational period at all, once `warp '' Q` is rigid. -/
theorem chair44_warp_main (Q : Set E) (g : ι → (E ≃ᵢ E)) [Nonempty ι]
    (hT : Tiling Q g) (hg : ∀ i, g i ∈ GammaGeom)
    (hper : ∀ v : E, IsSymmetry Q g (transl v) → v = 0) :
    Tiling (warp '' Q) g ∧
    (∀ b : V, bcc b → IsSymmetry (warp '' Q) g (transl (vec b)) → b = 0) ∧
    ((∀ σ : E ≃ᵢ E, σ '' (warp '' Q) = warp '' Q → σ = 1) →
      ∀ v : E, IsSymmetry (warp '' Q) g (transl v) → v = 0) ∧
    warp x0 ≠ x0 := by
  refine ⟨hT.warp GammaGeom warp warp_comm hg, ?_, ?_, warp_ne_id⟩
  · intro b hb hsym
    have h0 := hper _ ((symm_gamma_iff Q g hg (transl_mem hb)).mp hsym)
    funext i
    have := congrArg (fun z : E => z i) h0
    simpa using this
  · intro hrigid v hsym
    exact hper v (Tiling.warp_symm GammaGeom warp warp_comm hg hrigid hsym).2
