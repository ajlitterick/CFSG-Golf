module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionTransport

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointNormalizer

open CatalogueBOrthogonalPointAction

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)
variable {G : Type w} [Group G]
variable (ρ : G →* Equiv.Perm (Points Q)) (φ : Equiv.Perm (Points Q))

theorem normalizer_conjugate_exists
    (hφ : φ ∈ Subgroup.normalizer ρ.range) (g : G) :
    ∃ h : G, ρ h = φ * ρ g * φ⁻¹ :=
  ((Subgroup.mem_normalizer_iff.mp hφ) (ρ g)).mp ⟨g, rfl⟩

theorem normalizer_inverse_conjugate_exists
    (hφ : φ ∈ Subgroup.normalizer ρ.range) (g : G) :
    ∃ h : G, ρ h = φ⁻¹ * ρ g * φ :=
  ((Subgroup.mem_normalizer_iff''.mp hφ) (ρ g)).mp ⟨g, rfl⟩

theorem mem_actionStabilizerOrbit_normalizer_iff
    (hφ : φ ∈ Subgroup.normalizer ρ.range) (L M X : Points Q) :
    φ X ∈ actionStabilizerOrbit Q ρ (φ L) (φ M) ↔
      X ∈ actionStabilizerOrbit Q ρ L M := by
  rw [mem_actionStabilizerOrbit, mem_actionStabilizerOrbit]
  constructor
  · rintro ⟨g, hgL, hgM⟩
    obtain ⟨h, hh⟩ := normalizer_inverse_conjugate_exists Q ρ φ hφ g
    refine ⟨h, ?_, ?_⟩
    · rw [hh]
      change φ.symm (ρ g (φ L)) = L
      rw [hgL, φ.symm_apply_apply]
    · rw [hh]
      change φ.symm (ρ g (φ M)) = X
      rw [hgM, φ.symm_apply_apply]
  · rintro ⟨g, hgL, hgM⟩
    obtain ⟨h, hh⟩ := normalizer_conjugate_exists Q ρ φ hφ g
    refine ⟨h, ?_, ?_⟩
    · rw [hh]
      change φ (ρ g (φ.symm (φ L))) = φ L
      rw [φ.symm_apply_apply, hgL]
    · rw [hh]
      change φ (ρ g (φ.symm (φ M))) = φ X
      rw [φ.symm_apply_apply, hgM]


@[expose] def actionStabilizerOrbitNormalizerEquiv
    (hφ : φ ∈ Subgroup.normalizer ρ.range) (L M : Points Q) :
    actionStabilizerOrbit Q ρ L M ≃ actionStabilizerOrbit Q ρ (φ L) (φ M) where
  toFun X := ⟨φ X.val,
    (mem_actionStabilizerOrbit_normalizer_iff Q ρ φ hφ L M X.val).mpr X.property⟩
  invFun X := ⟨φ.symm X.val, by
    apply (mem_actionStabilizerOrbit_normalizer_iff Q ρ φ hφ L M (φ.symm X.val)).mp
    simpa only [φ.apply_symm_apply] using X.property⟩
  left_inv X := Subtype.ext (φ.symm_apply_apply X.val)
  right_inv X := Subtype.ext (φ.apply_symm_apply X.val)


theorem actionStabilizerOrbit_normalizer_card
    (hφ : φ ∈ Subgroup.normalizer ρ.range) (L M : Points Q) :
    Nat.card (actionStabilizerOrbit Q ρ L M) =
      Nat.card (actionStabilizerOrbit Q ρ (φ L) (φ M)) :=
  Nat.card_congr (actionStabilizerOrbitNormalizerEquiv Q ρ φ hφ L M)

end CFSG.ComponentClassification.CatalogueBOrthogonalPointNormalizer
