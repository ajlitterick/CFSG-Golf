module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G]

theorem aschProduct_eq_of_abelian (ambient generator : Subgroup G)
    (hcommutative : IsMulCommutative ambient) (hinclusion : generator ≤ ambient) :
    generator ⊔ (ambient ⊓ Subgroup.centralizer (generator : Set G)) = ambient := by
  have hcentralizer : ambient ≤ Subgroup.centralizer (generator : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hcommutative).trans
      (Subgroup.centralizer_le hinclusion)
  rw [inf_eq_left.mpr hcentralizer, sup_eq_right.mpr hinclusion]

theorem sylow_conjugate_eq_map (prime : ℕ) (sylowGroup : Sylow prime G) (conjugator : G) :
    ((conjugator • sylowGroup : Sylow prime G) : Subgroup G) =
      (sylowGroup : Subgroup G).map (MulAut.conj conjugator).toMonoidHom := by
  apply SetLike.coe_injective
  change ((conjugator • sylowGroup : Sylow prime G) : Set G) = _
  rw [Sylow.coe_smul, Subgroup.coe_map]
  rfl

theorem conjugate_map_mul (subgroup : Subgroup G) (outer inner : G) :
    (subgroup.map (MulAut.conj inner).toMonoidHom).map (MulAut.conj outer).toMonoidHom =
      subgroup.map (MulAut.conj (outer * inner)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext element
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  group

variable [Finite G]

theorem aschCore_eq_gamma_of_abelian (threshold prime : ℕ) (ambient : Subgroup G)
    (hcommutative : IsMulCommutative ambient) (hrank : 3 ≤ pRank prime ambient) :
    rankThreeAschCore threshold prime ambient = rankThreeGamma threshold prime ambient := by
  apply le_antisymm (aschCore_le_gamma threshold prime ambient)
  apply (gamma_le_iff threshold prime ambient _).mpr
  intro generator hinclusion hgeneratorRank
  apply aschCore_normalizer_le threshold prime ambient generator hinclusion hgeneratorRank
  rw [aschProduct_eq_of_abelian ambient generator hcommutative hinclusion]
  exact hrank


theorem pGroup_conjugate_into_sylow_within_overgroup (prime : ℕ) (hprime : prime.Prime)
    (sylowGroup : Sylow prime G) (overgroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup) (primeGroup : Subgroup G)
    (hpGroup : IsPGroup prime primeGroup) (hinclusion : primeGroup ≤ overgroup) :
    ∃ conjugator : overgroup,
      primeGroup.map (MulAut.conj (conjugator : G)).toMonoidHom ≤ (sylowGroup : Subgroup G) := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hinternal : IsPGroup prime (primeGroup.subgroupOf overgroup) :=
    hpGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hinclusion).symm
  obtain ⟨internalSylow, hcontained⟩ := hinternal.exists_le_sylow
  obtain ⟨conjugator, hconjugator⟩ := MulAction.IsPretransitive.exists_smul_eq (M := overgroup)
    internalSylow (sylowGroup.subtype hsylow)
  refine ⟨conjugator, ?_⟩
  rintro element ⟨source, hsource, rfl⟩
  let internalSource : overgroup := ⟨source, hinclusion hsource⟩
  have hinternalSource : internalSource ∈ internalSylow := hcontained hsource
  have hconjugateSource : (MulAut.conj conjugator) internalSource ∈
      ((conjugator • internalSylow : Sylow prime overgroup) : Subgroup overgroup) := by
    rw [sylow_conjugate_eq_map]
    exact Subgroup.mem_map_of_mem _ hinternalSource
  rw [hconjugator, Sylow.coe_subtype] at hconjugateSource
  exact hconjugateSource


end CFSG.RankThreeCoreUniqueness.Helpers
