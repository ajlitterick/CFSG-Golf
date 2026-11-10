module

public import CFSG.Sporadic.HNSchreier.ModuleCheckInputs
public import CFSG.Sporadic.HNSchreier.Seeds
public import CFSG.LinearAlgebra.CorankOneSpanning

public section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native Matrix
open CFSG.LinearAlgebra

instance hns_fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩


@[expose] noncomputable def matC : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  matB * matA * matB * matA + (3 : ZMod 5) • (matB * matA) + (2 : ZMod 5) • matB +
    (4 : ZMod 5) • (matA * matB * matB * matA) + matB * matB

theorem toMat_apply_133 (X : Array (Array ℕ)) (i j : Fin 133) :
    ((X[i.val]!)[j.val]! : ZMod 5) = toMat 5 133 X i j := rfl


theorem toMat_colsMat_eq_transpose (X : Array (Array ℕ)) :
    toMat 5 133 (colsMat 133 X) = (toMat 5 133 X)ᵀ := by
  ext i t
  rw [toMat_colsMat, Matrix.transpose_apply, toMat_apply, toVec_apply]


end CFSG.Sporadic.HNSchreier
