module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankOneCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerRankOneKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitContainmentTransfer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSemidihedralKernel
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open CFSG Subgroup CentralTwoActionKernel
open scoped commutatorElement Pointwise

namespace RankProjectiveAction

variable {H : Type*} [Group H]

theorem oddCore_eq_pPrimeCore (X : Type*) [Group X] : CFSG.oddCore X = pPrimeCore 2 X :=
  (CFSG.oddCore_eq_piCore X).trans (CFSG.pPrimeCore_eq_piCore X 2).symm

instance pLayer_two_normal {X : Type*} [Group X] [Finite X] : (pLayer X 2).Normal := by
  have := CatalogueBPrimeJoin.pLayer_characteristic (G := X) (p := 2)
  infer_instance


theorem exists_sylow_inf_of_le_normalizer [Finite H] {N S K : Subgroup H} (hSN : S ≤ N)
    (hS : ∃ T : Sylow 2 N, (T : Subgroup N) = S.subgroupOf N) (hKN : K ≤ N)
    (hK : N ≤ normalizer (K : Set H)) :
    ∃ T : Sylow 2 K, (T : Subgroup K) = (S ⊓ K).subgroupOf K := by
  obtain ⟨T, hT⟩ := hS
  have hKn : (K.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hKN).mpr hK
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal T hKn.isSubnormal
  let e : K.subgroupOf N ≃* K := subgroupOfEquivOfLe hKN
  have he : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨P.mapSurjective he, ?_⟩
  rw [Sylow.coe_mapSurjective]
  apply map_injective K.subtype_injective
  have hcomp : K.subtype.comp e.toMonoidHom = N.subtype.comp (K.subgroupOf N).subtype := by
    ext x
    rfl
  rw [map_map, subgroupOf_map_subtype, inf_assoc, inf_idem, hcomp, ← map_map, hP, hT,
    map_inf_eq _ _ N.subtype N.subtype_injective, subgroupOf_map_subtype,
    subgroupOf_map_subtype, inf_eq_left.mpr hSN, inf_eq_left.mpr hKN]


end RankProjectiveAction

open RankProjectiveAction


end CFSG.ComponentClassification.UnbalancedGS
