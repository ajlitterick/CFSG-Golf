module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflOrbit

public section

namespace CFSG.StandardType

open CFSG.Assembly


@[expose] def GGPseudoReflNbrStabModInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGInnerDiagOnLabel S p Bs K →
        ∀ φ ∈ ggAutomizer (Subgroup.centralizer ({y} : Set G)) Bs, GGIsPseudoReflection p φ →
          ∃ ψ ∈ ggAutomizer (ggG0 p B x L D J) Bs, (∀ b : ↥Bs, (b : G) = y → ψ b = b) ∧
            ∀ b : ↥Bs, (((ψ b)⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers y


theorem GGPseudoReflNbrStabModInputOn.or {S T : ℕ → LargeEvenLabel → Prop}
    (hS : GGPseudoReflNbrStabModInputOn S) (hT : GGPseudoReflNbrStabModInputOn T) :
    GGPseudoReflNbrStabModInputOn fun p lab => S p lab ∨ T p lab := by
  intro G _ _ p B Bs x L D J hH y K hyK hK
  rcases hK.elim_or with h | h
  · exact hS G p B Bs x L D J hH y K hyK h
  · exact hT G p B Bs x L D J hH y K hyK h


end CFSG.StandardType

end
