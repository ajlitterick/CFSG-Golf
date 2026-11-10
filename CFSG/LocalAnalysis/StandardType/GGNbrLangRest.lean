module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRestExc
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrLangRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ GGTypeASplitCoprimeLabel p lab ∧ ¬ GGLinearTwoLabel lab ∧ ¬ GGCorFourTwoOpenVacLabel p lab ∧
    ¬ GGNbrLangFieldTwoLabel lab ∧ ¬ GGLinearCoprimeDegLabel p lab ∧
    ¬ GGSpOmegaCoprimeDegLabel p lab ∧ ¬ GGExcCoprimeDegLabel p lab

@[expose] def GGNbrWeylRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ GGTypeASplitCoprimeLabel p lab ∧ ¬ GGLinearTwoLabel lab


theorem ggNbrInnerWeylOn_notTypeASplit_of_rest (h : GGNbrInnerWeylOn GGNbrWeylRestLabel) :
    GGNbrInnerWeylOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab := by
  refine (h.or ggNbrInnerWeylOn_linearTwo).mono ?_
  intro p lab hS
  by_cases h1 : GGLinearTwoLabel lab
  · exact Or.inr h1
  · exact Or.inl ⟨hS, h1⟩


end CFSG.StandardType

end
