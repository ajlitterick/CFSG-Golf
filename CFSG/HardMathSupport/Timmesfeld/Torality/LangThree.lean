module

public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly

public section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar

section


theorem langToralPlane_F4_three_of_bar (hbar : PlanesToralBar Tag.F4 3) :
    LangToralPlane Tag.F4 3 :=
  langToralPlane_of_bar Nat.prime_three hbar

theorem langToralPlane_E7_three_of_bar (hbar : PlanesToralBar Tag.E7 3) :
    LangToralPlane Tag.E7 3 :=
  langToralPlane_of_bar Nat.prime_three hbar

theorem langToralPlane_E8_three_of_bar (hbar : PlanesToralBar Tag.E8 3) :
    LangToralPlane Tag.E8 3 :=
  langToralPlane_of_bar Nat.prime_three hbar


theorem e8FiveToralPlane_of_bar (hbar : PlanesToralBar Tag.E8 5) : E8FiveToralPlane :=
  langToralPlane_E8_five_iff.1 (langToralPlane_of_bar (by norm_num) hbar)

end

end CFSG.HardMathSupport.Timmesfeld.Torality
