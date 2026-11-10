module

public import CFSG.LocalAnalysis.ZStar.PrincipalBlockCandidate

public section

namespace CFSG

namespace ZStar.BrauerSylowFusion

open ZStar.Helpers ZStar

universe u v

noncomputable section

abbrev groupAlgebraEquiv {H : Type u} {K : Type v}
    [Group H] [Group K] (e : H ≃* K) :
    GroupAlgebraTwo H ≃+* GroupAlgebraTwo K :=
  MonoidAlgebra.mapDomainRingEquiv (ZMod 2) e

@[simp]
theorem groupAlgebraEquiv_single {H : Type u} {K : Type v}
    [Group H] [Group K] (e : H ≃* K) (h : H) (r : ZMod 2) :
    groupAlgebraEquiv e (MonoidAlgebra.single h r) =
      MonoidAlgebra.single (e h) r := by
  exact MonoidAlgebra.mapDomainRingEquiv_single e r h

@[simp]
theorem groupAlgebraEquiv_coeff_apply {H : Type u} {K : Type v}
    [Group H] [Group K] (e : H ≃* K)
    (x : GroupAlgebraTwo H) (h : H) :
    (groupAlgebraEquiv e x).coeff (e h) = x.coeff h := by
  rw [MonoidAlgebra.coeff_mapDomainRingEquiv]
  simp


universe w

variable {G : Type w} [Group G] [Fintype G]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H


end

end ZStar.BrauerSylowFusion

end CFSG
