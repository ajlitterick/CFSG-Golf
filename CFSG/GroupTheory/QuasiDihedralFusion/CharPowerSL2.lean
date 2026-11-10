module

import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.QuasiDihedralFusion

open Matrix

universe u

section SL2

variable {F : Type u} [Field F]

@[expose] def sl2U : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

@[expose] def sl2T : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩

theorem coe_sl2U : ((sl2U : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![0, 1; -1, 0] := rfl

theorem coe_sl2T : ((sl2T : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![1, 1; 0, 1] := rfl

theorem coe_sl2U_mul_sl2U :
    ((sl2U * sl2U : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![-1, 0; 0, -1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2U]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_mem_center_iff {A : SpecialLinearGroup (Fin 2) F} :
    A ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ↔ A = 1 ∨ A = sl2U * sl2U := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    rw [Fintype.card_fin, sq] at hr
    rcases mul_self_eq_one_iff.mp hr with rfl | rfl
    · left
      ext i j
      rw [← hA]
      simp
    · right
      ext i j
      rw [← hA, coe_sl2U_mul_sl2U]
      fin_cases i <;> fin_cases j <;> simp
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · refine ⟨-1, by simp, ?_⟩
      rw [coe_sl2U_mul_sl2U]
      ext i j
      fin_cases i <;> fin_cases j <;> simp


theorem sq_mem_range_toPGL (g : ProjGenLinGroup (Fin 2) F) :
    g ^ 2 ∈ (Matrix.SpecialLinearGroup.toPGL :
      SpecialLinearGroup (Fin 2) F →* ProjGenLinGroup (Fin 2) F).range := by
  obtain ⟨x, hx⟩ := CFSG.GorensteinWalter.pgl2_sq_mem_psl2Range g
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨s, hx⟩

end SL2

end CFSG.QuasiDihedralFusion
