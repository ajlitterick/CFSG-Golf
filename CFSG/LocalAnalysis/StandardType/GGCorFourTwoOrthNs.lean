module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMore
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNine

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


section FromLID


theorem ggTableBCxInputOn_of_orthNs {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGOrthNsLabel p lab) (hD : GGBstarInnerDiagLInputOn S) :
    GGTableBCxInputOn S :=
  ggTableBCxInputOn_of_irred hD (ggTableBIrredInputOn_orthNs.mono hS)

theorem ggTableBModuleInputOn_of_orthNs {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGOrthNsLabel p lab) (hD : GGBstarInnerDiagLInputOn S) :
    GGTableBModuleInputOn S :=
  ggTableBModuleInputOn_of_irred hD (ggTableBIrredInputOn_orthNs.mono hS)

theorem ggTableBActionInputOn_of_orthNs {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGOrthNsLabel p lab) (hD : GGBstarInnerDiagLInputOn S) :
    GGTableBActionInputOn S :=
  ggTableBActionInputOn_of_irred hD (ggTableBIrredInputOn_orthNs.mono hS)

theorem ggTableBNbrInnerInputOn_of_not_orthNs {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBNbrInnerInputOn fun p lab => S p lab ∧ ¬ GGOrthNsLabel p lab) :
    GGTableBNbrInnerInputOn S :=
  (ggTableBNbrInnerInputOn_orthNs.or h).mono fun p lab hS => by
    by_cases h' : GGOrthNsLabel p lab
    · exact Or.inl h'
    · exact Or.inr ⟨hS, h'⟩


theorem ggLNoInvariantLineInputOn_of_not_orthNs {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLNoInvariantLineInputOn fun p lab => S p lab ∧ ¬ GGOrthNsLabel p lab) :
    GGLNoInvariantLineInputOn S := by
  have h' := ggLNoInvariantLineInputOn_orthNs.or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases h1 : GGOrthNsLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩


end FromLID


section Certs


theorem ggTableBCxInputOn_of_not_orthNsVac {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGOrthNsVacLabel p lab) :
    GGTableBCxInputOn S :=
  ((ggTableBCxInputOn_orthNsVac ggLNoncyclicInput_holds).or h).mono fun p lab hS => by
    by_cases h3 : GGOrthNsVacLabel p lab
    · exact Or.inl h3
    · exact Or.inr ⟨hS, h3⟩


theorem ggTableBModuleInputOn_of_not_orthNsVac {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGOrthNsVacLabel p lab) :
    GGTableBModuleInputOn S :=
  ((ggTableBModuleInputOn_orthNsVac ggLNoncyclicInput_holds).or h).mono fun p lab hS => by
    by_cases h3 : GGOrthNsVacLabel p lab
    · exact Or.inl h3
    · exact Or.inr ⟨hS, h3⟩


theorem ggTableBActionInputOn_of_not_orthNsVac {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGOrthNsVacLabel p lab) :
    GGTableBActionInputOn S :=
  ((ggTableBActionInputOn_orthNsVac ggLNoncyclicInput_holds).or h).mono fun p lab hS => by
    by_cases h3 : GGOrthNsVacLabel p lab
    · exact Or.inl h3
    · exact Or.inr ⟨hS, h3⟩


end Certs

end CFSG.StandardType

end
