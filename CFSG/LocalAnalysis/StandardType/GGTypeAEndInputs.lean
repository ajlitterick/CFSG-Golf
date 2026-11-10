module

public import CFSG.LocalAnalysis.StandardType.GGTypeAEndInputsUnique

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix


section Model

variable {F : Type} [Field F]


end Model


@[expose] def GGTypeAJoinAutInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K →
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs → K' ≤ L ⊔ K

@[expose] def GGTypeAJoinReflInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K →
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      ¬ ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs → p ∣ n + 3

theorem ggTypeAJoinInput_of_aut_refl (h₁ : GGTypeAJoinAutInput) (h₂ : GGTypeAJoinReflInput) :
    GGTypeAJoinInput := by
  intro G _ _ p B Bs x L D J n f y K hN y' K' hK'
  obtain ⟨-, -, -, -, -, -, -, hp3, -⟩ := id hN
  by_contra hle
  exact hp3 (h₂ G p B Bs x L D J n f y K hN y' K' hK'
    fun hA => hle (h₁ G p B Bs x L D J n f y K hN y' K' hK' hA))

end CFSG.StandardType
