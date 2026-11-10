module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Matrix

private def S0 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1,1,0;0,1,0;0,0,1]

private theorem S0_det_ne_zero : S0.det ≠ 0 := by decide +kernel

private def s0 : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero S0 S0_det_ne_zero


theorem card_GL32 : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field (𝔽 := ZMod 2) 3]
  norm_num [Fin.prod_univ_three]

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
