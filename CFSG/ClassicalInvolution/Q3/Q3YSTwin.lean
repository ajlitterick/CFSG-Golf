module

public import CFSG.ClassicalInvolution.Q3.Q3YSComp
public import CFSG.ClassicalInvolution.Q3.Q3YComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

section Quat

def qw : SL(2, ZMod 3) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

def qu : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩


theorem neg_one_ne_one : (-1 : SL(2, ZMod 3)) ≠ 1 := by decide +kernel


end Quat

section Algebra


end Algebra

structure KleinQuat (M : Type*) [Group M] (y y' : M) : Prop where
  comm : y * y' = y' * y
  sq_eq : y * y = y' * y'
  sq_central : y * y ∈ Subgroup.center M
  sq_sq : (y * y) * (y * y) = 1
  not_central : y ∉ Subgroup.center M
  not_central' : y' ∉ Subgroup.center M
  prod_not_central : y * y' ∉ Subgroup.center M

section Lie


end Lie

end CFSG.ClassicalInvolution.Q3.Q3YS
