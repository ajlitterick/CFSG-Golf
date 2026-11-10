module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSubgroup

open scoped MatrixGroups

section

@[expose] noncomputable def upper (F : Type) [Field F] : Multiplicative F →* SL(2, F) where
  toFun a := ⟨!![1, a.toAdd; 0, 1], by simp [Matrix.det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    show (!![1, (a * b).toAdd; 0, 1] : Matrix (Fin 2) (Fin 2) F) =
      !![1, a.toAdd; 0, 1] * !![1, b.toAdd; 0, 1]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem upper_apply_zero_one {F : Type} [Field F] (a : Multiplicative F) :
    ((upper F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 = a.toAdd := rfl

theorem psl_upper_injective {F : Type} [Field F] :
    Function.Injective
      ((QuotientGroup.mk' (Subgroup.center SL(2, F))).comp (upper F) :
        Multiplicative F →* PSL(2, F)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hc : upper F a ∈ Subgroup.center SL(2, F) := by
    simpa using (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have : a.toAdd = 0 := by
    rw [← upper_apply_zero_one, ← hr]; simp [Matrix.scalar_apply]
  exact toAdd_eq_zero.mp this

end


end CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSubgroup
