module

public import CFSG.Sporadic.Recognition.McLMultiplierInputs
public import CFSG.Sporadic.McL.VecSpec

public section

namespace CFSG.Sporadic.Recognition.McLMultiplier

open CFSG.F3.Native CFSG.LieType.Multipliers CFSG.Sporadic.VecOrbit

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Eval

variable (E Ei : ℕ → Array V)


end Eval

theorem coverRelators_mclCommW : coverRelators (wordSet mclRels) mclCommW = wordSet mclCover :=
  coverRelators_wordSet mclRels mclCommWord


end CFSG.Sporadic.Recognition.McLMultiplier
