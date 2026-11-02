module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Main
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Main
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Main
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Main

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap

theorem pairFrame_exc {p e : ℕ} [Fact p.Prime] [NeZero e] {t : StatedLieTag}
    (ht : t = .E8 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t 0 p e) :
    PairFrame (excSignGroup t p e) (fundamentalSubgroups t (modelUniv t 0 p e Fact.out).D) := by
  rcases ht with rfl | rfl | rfl | rfl
  · exact pairFrame_e8 hp2 hadm
  · exact pairFrame_f4 hp2 hadm
  · exact pairFrame_e6 hp2 hadm
  · exact pairFrame_e7 hp2 hadm

end CFSG.ClassicalInvolution.ModelFacts
