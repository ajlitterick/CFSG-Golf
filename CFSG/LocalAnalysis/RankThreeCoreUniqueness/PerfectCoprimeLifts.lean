module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralComponentLifts

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers


theorem normal_subgroupOf_comap
    {G Image : Type*} [Group G] [Group Image] (homomorphism : G →* Image)
    (subgroup overgroup : Subgroup Image) (hbound : subgroup ≤ overgroup)
    (hnormal : (subgroup.subgroupOf overgroup).Normal) :
    ((Subgroup.comap homomorphism subgroup).subgroupOf
      (Subgroup.comap homomorphism overgroup)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff (Subgroup.comap_mono hbound)).mpr
  intro element conjugator helement hconjugator
  change homomorphism (conjugator * element * conjugator⁻¹) ∈ subgroup
  rw [map_mul, map_mul, map_inv]
  exact (Subgroup.normal_subgroupOf_iff hbound).mp hnormal
    (homomorphism element) (homomorphism conjugator) helement hconjugator

theorem cfsg_isSubnormal_comap
    {G Image : Type*} [Group G] [Group Image] (homomorphism : G →* Image)
    {subgroup overgroup : Subgroup Image} (hsubnormal : IsSubnormal subgroup overgroup) :
    IsSubnormal (Subgroup.comap homomorphism subgroup) (Subgroup.comap homomorphism overgroup) :=
  hsubnormal.comap homomorphism


end CFSG.RankThreeCoreUniqueness.Helpers
