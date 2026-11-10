
module


public import CFSG.Monster.B.TwoA.Sp8.SubgeomIso
public import CFSG.Monster.B.TwoA.Sp8.SubgeomCard

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open Module Submodule Matrix CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open LinearMap (BilinForm)

attribute [local instance] parAction subgeomAction

attribute [local instance] parAction subgeomAction

theorem J_eq_fromBlocks (r : ℕ) : Matrix.J (Fin r) (ZMod 2) = fromBlocks 0 1 (-1) 0 := by
  ext (i | i) (j | j) <;> simp [Matrix.J, Matrix.one_apply]


end CFSG.Monster.B.TwoA.Sp8
