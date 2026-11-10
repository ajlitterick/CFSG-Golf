module

public import CFSG.Milestones.ASVolI.A3Aut.C5Base
public import CFSG.Milestones.ASVolI.A3Aut.SBSp4
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Std
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.Milestones.ASVolI.A3Aut.Fam
public import CFSG.Milestones.ASVolI.A3Aut.Util

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

section C5Sp4

variable {K : Type} [Field K] [Finite K]


theorem burnsideAut_c5Sp4_inn_inf_field :
    (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ⊓
      (SymplecticHigher.fieldAut 2 K).range = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨hφI, ⟨σ, rfl⟩⟩
  have h1 := (CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_range_conjAut_iff (r := 2) (K := K)
    (by norm_num)).1 (CFSG.RankThree.PartTwo.KFacts.innAut_le_range_spConjAut 2 K hφI)
  rw [h1, map_one]
  exact Subgroup.one_mem _

theorem burnsideAut_c5Sp4_odd_mem [CharP K 2] {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα : Odd (orderOf α)) :
    α ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ⊔
      (SymplecticHigher.fieldAut 2 K).range := by
  obtain ⟨A, σ, hAσ⟩ := (SymplecticHigher.mem_spSemilinearAutGroup_iff (r := 2) (K := K)).1
    (CFSG.RankThree.PartOne.CTP.mem_spSemilinearAutGroup_of_odd_pow hα (pow_orderOf_eq_one α))
  rw [hAσ]
  exact Subgroup.mul_mem_sup (CFSG.RankThree.PartTwo.KFacts.conjAut_mem_inner_of_charTwo A)
    ⟨σ, rfl⟩


end C5Sp4

end CFSG.ASVolI
