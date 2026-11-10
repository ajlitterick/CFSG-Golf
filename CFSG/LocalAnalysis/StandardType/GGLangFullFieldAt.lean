module

public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput
import CFSG.LocalAnalysis.StandardType.GGCompFieldLieModel
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.ComponentClassification.CatLeafProof

@[expose] def LangFullFieldAt : Prop :=
  ∀ (τ : Tag), (τ = .E7 ∨ τ = .E8) → ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
    GGCompFieldAt (Nat.card K) (⊤ : Subgroup ↥(adjointGroup τ K))

theorem langFullFieldAt_holds
    : LangFullFieldAt := by
  intro τ hτ K _ _ _
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hk : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hZ : Subgroup.center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hqs : CFSG.IsQuasisimple ↥(adjointGroup τ K) := by
    rcases hτ with rfl | rfl
    · exact CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K
    · exact isQuasisimple_e8 K
  have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup ↥(adjointGroup τ K)) := by
    have h := CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(adjointGroup τ K)) ≃* ↥(adjointGroup τ K)) hqs
    exact ⟨h.1.commutator_eq_top, h.2.1⟩
  have key : ∀ t : StatedLieTag, (t = .E7 ∧ τ = .E7 ∨ t = .E8 ∧ τ = .E8) →
      GGCompFieldAt (2 ^ (f : ℕ)) (⊤ : Subgroup ↥(adjointGroup τ K)) := by
    intro t htτ
    obtain ⟨-, hM⟩ := lieModel_of_mulEquiv_adjointGroup_E7_E8 htτ f.pos hk (MulEquiv.refl _)
    have hM' := LieModel.quotient_center_of_mulEquiv
      (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(adjointGroup τ K)) ≃* ↥(adjointGroup τ K)).symm
      (hM.quotient_center hZ)
    refine ggCompFieldAt_of_lieModel hq hM' ⟨?_, ?_, ?_⟩ <;>
      rcases htτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  rw [hk]
  rcases hτ with rfl | rfl
  · exact key .E7 (Or.inl ⟨rfl, rfl⟩)
  · exact key .E8 (Or.inr ⟨rfl, rfl⟩)

end CFSG.StandardType.LangRat
