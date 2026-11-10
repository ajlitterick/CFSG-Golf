module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSplit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbitBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CatalogueBOrthogonalSmallFamilyOrbit
open scoped Pointwise


variable (n : ℕ) (K : Type) [Field K]


theorem plusProjectiveUnipotent_isSylow [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (hn : 3 ≤ n) :
    ∃ S : Sylow p (StatedProj (StatedOmega (StatedQuadPlus n K))),
      (S : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) =
        plusProjectiveUnipotent n K := by
  have : Finite (orthElementaryGroup (quadPlus n K)) := finite_orthElementaryGroup
  obtain ⟨S, hS⟩ := projUnip_isSylow (K := K) p hn
  have hsurj : Function.Surjective (plusProjectiveEquiv n K hn).symm.toMonoidHom :=
    (plusProjectiveEquiv n K hn).symm.surjective
  refine ⟨Sylow.mapSurjective (f := (plusProjectiveEquiv n K hn).symm.toMonoidHom) hsurj S,
    ?_⟩
  rw [Sylow.coe_mapSurjective, hS, ← plusProjectiveUnipotent_map n K hn, Subgroup.map_map]
  have he : (plusProjectiveEquiv n K hn).symm.toMonoidHom.comp
      (plusProjectiveEquiv n K hn).toMonoidHom = MonoidHom.id _ := by
    ext x
    exact (plusProjectiveEquiv n K hn).symm_apply_apply x
  rw [he, Subgroup.map_id]

theorem plusProjectiveUnipotent_normalizer [Finite K] (hn : 3 ≤ n) :
    Subgroup.normalizer (plusProjectiveUnipotent n K :
      Set (StatedProj (StatedOmega (StatedQuadPlus n K)))) = plusProjectiveBorel n K := by
  apply Subgroup.map_injective (f := (plusProjectiveEquiv n K hn).toMonoidHom)
    (plusProjectiveEquiv n K hn).injective
  rw [Subgroup.map_equiv_normalizer_eq, plusProjectiveUnipotent_map,
    normalizer_projUnip hn, plusProjectiveBorel_map]


end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
