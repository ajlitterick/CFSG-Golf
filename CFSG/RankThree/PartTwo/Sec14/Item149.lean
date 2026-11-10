module

public import CFSG.RankThree.PartTwo.Sec14.Item14Statements
public import CFSG.RankThree.PartTwo.Sec14.Item145
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.Transfer.Yoshida
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.GH74.GLS

variable {G : Type*} [Group G]

theorem mem_oResidual_two_of_pow_three {D : Subgroup G} {x : G} (hx : x ∈ D) {k : ℕ}
    (hk : x ^ 3 ^ k = 1) : x ∈ inSubgroup (oResidual 2) D := by
  rw [inSubgroup_oResidual_eq_closure]
  refine Subgroup.subset_closure ⟨hx, ?_⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  rw [hj]
  exact Nat.Coprime.pow_left j (by norm_num)


end CFSG.RankThree.PartTwo.Sec14
