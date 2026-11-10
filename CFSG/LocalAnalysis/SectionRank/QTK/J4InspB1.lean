module

public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharEven
public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA4

public section

namespace CFSG.SectionRank.QTK

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf


theorem sp6TwoOrder_holds :
    Sp6TwoOrder := by
  intro H _ hH
  have hLM : CFSG.Blueprint.LieModel H .PSp 3 2 1 := Or.inl ⟨by decide, hH⟩
  have hM := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput H .PSp 3 2 1
    hH.1 hLM).2.1
  have hd : lieOrderDivisor .PSp 3 (2 ^ 1) = 1 := by decide
  have hn : lieOrderNumerator .PSp 3 (2 ^ 1) = 1451520 := by decide
  rw [hd, hn, Nat.mul_one] at hM
  exact hM


end CFSG.SectionRank.QTK
