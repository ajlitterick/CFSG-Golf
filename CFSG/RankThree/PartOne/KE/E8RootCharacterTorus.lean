module

public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

@[expose] def cartanInvE8 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3; 7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5; 6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2]

theorem cartanInvE8_mul : cartanInvE8 * Tag.E8.cartan = 1 := by
  decide +kernel

theorem rootDiagUnit_E8_mem_torusGroup {M : Type} [Field M] (a : Fin Tag.E8.rank → Mˣ) :
    rootDiagUnit Tag.E8 a ∈ torusGroup Tag.E8 M := by
  rw [rootDiagUnit_eq_list_prod_torusElt (K := M) cartanInvE8_mul a]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact torusElt_mem_torusGroup i _

theorem rootDiagUnit_E8_mem_adjointGroup {M : Type} [Field M] (a : Fin Tag.E8.rank → Mˣ) :
    rootDiagUnit Tag.E8 a ∈ adjointGroup Tag.E8 M := by
  rw [rootDiagUnit_eq_list_prod_torusElt (K := M) cartanInvE8_mul a]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact torusElt_mem_adjointGroup i _


end CFSG.RankThree.PartOne.KE
