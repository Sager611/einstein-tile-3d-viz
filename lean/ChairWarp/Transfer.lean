import Mathlib

/-!
# Equivariant warps transfer tilings and their symmetries

`X` is a metric space (in the application, Euclidean 3-space), `Γ` a group of isometries,
`Q` a prototile and `g : ι → (X ≃ᵢ X)` the placements of a tiling by copies `g i '' Q`.

* `Tiling.warp`: a homeomorphism `Φ` commuting with every element of `Γ` sends a tiling whose
  placements lie in `Γ` to a tiling by the congruent copies `g i '' (Φ '' Q)`.
* `Tiling.warp_symm`: if moreover `Φ '' Q` has no non-identity self-isometry, every symmetry of
  the warped tiling lies in `Γ` and is already a symmetry of the original tiling. In particular a
  warp of a non-periodic tiling is non-periodic.
-/

open Set

variable {X : Type*} [MetricSpace X] {ι : Type*}

/-- A family of isometric copies of `Q` covering `X` with pairwise disjoint interiors. -/
structure Tiling (Q : Set X) (g : ι → (X ≃ᵢ X)) : Prop where
  cover : (⋃ i, g i '' Q) = univ
  disjoint : Pairwise fun i j => Disjoint (interior (g i '' Q)) (interior (g j '' Q))

/-- An isometry `τ` is a symmetry of the tile family if it permutes the tiles. -/
def IsSymmetry (Q : Set X) (g : ι → (X ≃ᵢ X)) (τ : X ≃ᵢ X) : Prop :=
  (∀ i, ∃ j, τ '' (g i '' Q) = g j '' Q) ∧ ∀ j, ∃ i, τ '' (g i '' Q) = g j '' Q

section Warp

variable (Γ : Subgroup (X ≃ᵢ X)) (Φ : X ≃ₜ X)

/-- Equivariance turns a warped copy into the warp of a copy. -/
lemma image_warp_comm (hΦ : ∀ γ ∈ Γ, ∀ x, Φ (γ x) = γ (Φ x)) {γ : X ≃ᵢ X} (hγ : γ ∈ Γ)
    (S : Set X) : γ '' (Φ '' S) = Φ '' (γ '' S) := by
  rw [image_image, image_image]
  exact image_congr fun x _ => (hΦ γ hγ x).symm

theorem Tiling.warp {Q : Set X} {g : ι → (X ≃ᵢ X)} (hT : Tiling Q g)
    (hΦ : ∀ γ ∈ Γ, ∀ x, Φ (γ x) = γ (Φ x)) (hg : ∀ i, g i ∈ Γ) :
    Tiling (Φ '' Q) g := by
  have key : ∀ i, g i '' (Φ '' Q) = Φ '' (g i '' Q) := fun i => image_warp_comm Γ Φ hΦ (hg i) Q
  refine ⟨?_, ?_⟩
  · simp_rw [key, ← image_iUnion, hT.cover, image_univ_of_surjective Φ.surjective]
  · intro i j hij
    rw [key, key, ← Φ.image_interior, ← Φ.image_interior,
      disjoint_image_iff Φ.injective]
    exact hT.disjoint hij

theorem Tiling.warp_symm {Q : Set X} {g : ι → (X ≃ᵢ X)} [Nonempty ι]
    (hΦ : ∀ γ ∈ Γ, ∀ x, Φ (γ x) = γ (Φ x)) (hg : ∀ i, g i ∈ Γ)
    (hrigid : ∀ σ : X ≃ᵢ X, σ '' (Φ '' Q) = Φ '' Q → σ = 1)
    {τ : X ≃ᵢ X} (hτ : IsSymmetry (Φ '' Q) g τ) :
    τ ∈ Γ ∧ IsSymmetry Q g τ := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨j, hj⟩ := hτ.1 i
  -- `(g j)⁻¹ * τ * g i` fixes the warped tile, hence is the identity.
  have hσ : ⇑((g j)⁻¹ * τ * g i) '' (Φ '' Q) = Φ '' Q := by
    calc ⇑((g j)⁻¹ * τ * g i) '' (Φ '' Q)
        = ⇑((g j)⁻¹) '' (τ '' (g i '' (Φ '' Q))) := by
          simp only [image_image]; rfl
      _ = ⇑((g j)⁻¹) '' (g j '' (Φ '' Q)) := by rw [hj]
      _ = Φ '' Q := by
          rw [image_image]
          have : ∀ x, ((g j)⁻¹) ((g j) x) = x := fun x => (g j).symm_apply_apply x
          simp only [this, image_id']
  have hτΓ : τ ∈ Γ := by
    have h1 := hrigid _ hσ
    have : τ = g j * (g i)⁻¹ := by
      rw [← mul_inv_eq_one, mul_inv_rev, inv_inv, ← mul_assoc]
      have : (g j)⁻¹ * τ * g i = 1 := h1
      calc τ * g i * (g j)⁻¹ = g j * ((g j)⁻¹ * τ * g i) * (g j)⁻¹ := by group
        _ = 1 := by rw [this]; group
    rw [this]
    exact Γ.mul_mem (hg j) (Γ.inv_mem (hg i))
  refine ⟨hτΓ, ?_, ?_⟩
  · intro k
    obtain ⟨l, hl⟩ := hτ.1 k
    refine ⟨l, ?_⟩
    apply (image_injective.mpr Φ.injective)
    rw [← image_warp_comm Γ Φ hΦ hτΓ, ← image_warp_comm Γ Φ hΦ (hg k),
      ← image_warp_comm Γ Φ hΦ (hg l), hl]
  · intro l
    obtain ⟨k, hk⟩ := hτ.2 l
    refine ⟨k, ?_⟩
    apply (image_injective.mpr Φ.injective)
    rw [← image_warp_comm Γ Φ hΦ hτΓ, ← image_warp_comm Γ Φ hΦ (hg k),
      ← image_warp_comm Γ Φ hΦ (hg l), hk]

end Warp

section Periods

variable (Γ : Subgroup (X ≃ᵢ X)) (Φ : X ≃ₜ X)

/-- Non-periodicity transfers: if the only symmetries of the original tiling satisfying a
property `P` (for instance "is a nonzero translation") are excluded, the same holds for the
warp. -/
theorem Tiling.warp_no_symmetry {Q : Set X} {g : ι → (X ≃ᵢ X)} [Nonempty ι]
    (hΦ : ∀ γ ∈ Γ, ∀ x, Φ (γ x) = γ (Φ x)) (hg : ∀ i, g i ∈ Γ)
    (hrigid : ∀ σ : X ≃ᵢ X, σ '' (Φ '' Q) = Φ '' Q → σ = 1)
    (P : (X ≃ᵢ X) → Prop) (hQ : ∀ τ, IsSymmetry Q g τ → ¬ P τ) :
    ∀ τ, IsSymmetry (Φ '' Q) g τ → ¬ P τ := fun τ hτ =>
  hQ τ (Tiling.warp_symm Γ Φ hΦ hg hrigid hτ).2

end Periods
