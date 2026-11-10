module

public import CFSG.LieType.Chevalley.WeylSpace
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley Matrix


theorem symmetrizedCartan_isSymm (τ : Tag) : τ.symmetrizedCartan.IsSymm := by
  cases τ <;> decide +kernel


end CFSG.LieType.Chevalley
