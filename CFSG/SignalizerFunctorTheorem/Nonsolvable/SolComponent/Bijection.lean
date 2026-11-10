module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Defs

public section

namespace CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {G : Type*} [Group G]

theorem comap_map_mk'_eq (K R : Subgroup G) [R.Normal] :
    (K.map (QuotientGroup.mk' R)).comap (QuotientGroup.mk' R) = K ⊔ R := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem exists_perfect_isSubnormal_map_eq [Finite G] {R : Subgroup G} [R.Normal]
    {C : Subgroup (G ⧸ R)} (hCp : Group.IsPerfect C) (hCs : C.IsSubnormal) :
    Group.IsPerfect ((CFSG.perfectResidual (C.comap (QuotientGroup.mk' R))).map
        (C.comap (QuotientGroup.mk' R)).subtype) ∧
      ((CFSG.perfectResidual (C.comap (QuotientGroup.mk' R))).map
        (C.comap (QuotientGroup.mk' R)).subtype).IsSubnormal ∧
      ((CFSG.perfectResidual (C.comap (QuotientGroup.mk' R))).map
        (C.comap (QuotientGroup.mk' R)).subtype).map (QuotientGroup.mk' R) = C := by
  refine ⟨isPerfect_perfectResidual_map _, isSubnormal_perfectResidual_map (hCs.comap _), ?_⟩
  rw [map_perfectResidual_map, Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective R)]
  exact perfectResidual_map_eq_of_isPerfect hCp


namespace IsSolComponent

variable {K L : Subgroup G}

theorem not_isSolvable (hK : IsSolComponent K) : ¬ Group.IsSolvable K := by
  intro hs
  have := hK.isPerfect
  have hnt : Nontrivial (K.map (QuotientGroup.mk' (CFSG.solvableRadical G))) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hK.isComponent_map.1
  have : Nontrivial K := Function.Surjective.nontrivial
    ((QuotientGroup.mk' (CFSG.solvableRadical G)).subgroupMap_surjective K)
  exact Group.IsPerfect.not_isSolvable K hs

variable [Finite G]


theorem le_of_map_le_map (hK : IsSolComponent K) {S : Subgroup G} (hS : S.IsSubnormal)
    (h : K.map (QuotientGroup.mk' (CFSG.solvableRadical G)) ≤
      S.map (QuotientGroup.mk' (CFSG.solvableRadical G))) : K ≤ S := by
  have hRs : Group.IsSolvable (CFSG.solvableRadical G) := isSolvable_solvableRadical
  have := hK.isPerfect
  have hKb : Group.IsPerfect (K.map (QuotientGroup.mk' (CFSG.solvableRadical G))) :=
    Group.IsPerfect.map _
  have h1 : K.map (QuotientGroup.mk' (CFSG.solvableRadical G)) ≤
      ((CFSG.perfectResidual S).map S.subtype).map
        (QuotientGroup.mk' (CFSG.solvableRadical G)) := by
    rw [map_perfectResidual_map]
    exact le_perfectResidual_map_of_isPerfect hKb h
  have h2 : K ≤ (CFSG.perfectResidual S).map S.subtype ⊔ CFSG.solvableRadical G := by
    have := Subgroup.map_le_iff_le_comap.mp h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
  exact (le_of_le_sup_of_isPerfect (R := CFSG.solvableRadical G) hK.isPerfect
    (isPerfect_perfectResidual_map S) (isSubnormal_perfectResidual_map hS) inferInstance hRs
    h2).trans (Subgroup.map_subtype_le _)

theorem eq_of_map_eq (hK : IsSolComponent K) (hL : IsSolComponent L)
    (h : K.map (QuotientGroup.mk' (CFSG.solvableRadical G)) =
      L.map (QuotientGroup.mk' (CFSG.solvableRadical G))) : K = L :=
  le_antisymm (hK.le_of_map_le_map hL.isSubnormal h.le) (hL.le_of_map_le_map hK.isSubnormal h.ge)


end IsSolComponent

theorem exists_isSolComponent_map_eq [Finite G] {C : Subgroup (G ⧸ CFSG.solvableRadical G)}
    (hC : CFSG.IsComponent C) :
    ∃ K : Subgroup G, IsSolComponent K ∧
      K.map (QuotientGroup.mk' (CFSG.solvableRadical G)) = C := by
  obtain ⟨hp, hs, hmap⟩ := exists_perfect_isSubnormal_map_eq (R := CFSG.solvableRadical G)
    hC.1.1 hC.2
  exact ⟨_, ⟨hp, hs, by rw [hmap]; exact hC⟩, hmap⟩


theorem map_solLayer_eq_layer [Finite G] :
    (solLayer G).map (QuotientGroup.mk' (CFSG.solvableRadical G)) =
      CFSG.layer (G ⧸ CFSG.solvableRadical G) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    have hKc : IsSolComponent K := hK
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup hKc.isComponent_map
  · refine sSup_le fun C hC => ?_
    obtain ⟨K, hK, rfl⟩ := exists_isSolComponent_map_eq hC
    exact Subgroup.map_mono (le_solLayer hK)

theorem oStar_eq_comap_layer [Finite G] :
    oStar G = (CFSG.layer (G ⧸ CFSG.solvableRadical G)).comap
      (QuotientGroup.mk' (CFSG.solvableRadical G)) := by
  rw [← map_solLayer_eq_layer, comap_map_mk'_eq]
  exact sup_comm _ _

end CFSG.SignalizerFunctorTheorem.Nonsolvable
