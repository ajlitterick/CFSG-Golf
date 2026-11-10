module

public import CFSG.LieType.SteinbergBRSemidirectRadical
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.LieType.SteinbergBR

open Matrix SemidirectProduct

variable {F : Type*} [Field F]

theorem mem_center_SL2_iff {A : SpecialLinearGroup (Fin 2) F} :
    A ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ↔ A.val = 1 ∨ A.val = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  constructor
  · rintro ⟨r, hr, hA⟩
    rcases sq_eq_one_iff.1 hr with rfl | rfl
    · left
      rw [← hA, map_one]
    · right
      rw [← hA, map_neg, map_one]
  · rintro (h | h)
    · exact ⟨1, one_pow 2, by rw [map_one]; exact h.symm⟩
    · exact ⟨-1, by norm_num, by rw [map_neg, map_one]; exact h.symm⟩

theorem card_center_SL2_eq_two (hF : ringChar F ≠ 2) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) F)) = 2 := by
  have hne : (1 : SpecialLinearGroup (Fin 2) F) ≠ -1 := by
    intro h
    have h00 := congrArg (fun A : SpecialLinearGroup (Fin 2) F => A.val 0 0) h
    change (1 : Matrix (Fin 2) (Fin 2) F) 0 0 = -((1 : Matrix (Fin 2) (Fin 2) F) 0 0) at h00
    rw [Matrix.one_apply_eq] at h00
    exact Ring.neg_one_ne_one_of_char_ne_two hF h00.symm
  have hset : ((Subgroup.center (SpecialLinearGroup (Fin 2) F) :
      Set (SpecialLinearGroup (Fin 2) F))) = {1, -1} := by
    ext A
    rw [SetLike.mem_coe, mem_center_SL2_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact or_congr (Subtype.ext_iff (a1 := A) (a2 := (1 : SpecialLinearGroup (Fin 2) F))).symm
      (Subtype.ext_iff (a1 := A) (a2 := (-1 : SpecialLinearGroup (Fin 2) F))).symm
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_pair hne]


end CFSG.LieType.SteinbergBR
