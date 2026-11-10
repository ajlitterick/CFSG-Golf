module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Matrix


theorem card_GL32 : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field (𝔽 := ZMod 2) 3]
  norm_num [Fin.prod_univ_three]

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
