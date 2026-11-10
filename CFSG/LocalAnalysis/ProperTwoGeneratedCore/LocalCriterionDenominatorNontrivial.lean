module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorFixedSets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCoreCover

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.SignalizerFunctor.Helpers
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem normalizer_normalizes_oddCore_image (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (((oddCore D).map D.subtype : Subgroup G) : Set G) := by
  intro s hs
  let phi : MulAut D := D.normalizerMonoidHom ⟨s, hs⟩
  have hhom : (MulAut.conj s).toMonoidHom.comp D.subtype =
      D.subtype.comp phi.toMonoidHom := by
    ext d
    rfl
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change ((oddCore D).map D.subtype).map (MulAut.conj s).toMonoidHom = _
  rw [Subgroup.map_map, hhom, ← Subgroup.map_map]
  have hphi : (oddCore D).map phi.toMonoidHom = oddCore D :=
    CFSG.ComponentClassification.OddCore.char_invariant phi
  rw [hphi]

theorem commute_normalizes_centralizer (s t : G) (hst : Commute s t) :
    s ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) := by
  have hN : Subgroup.normalizer ({t} : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer ({t} : Set G))).mp inferInstance
  apply hN
  rw [Subgroup.normalizer_singleton]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hst.eq

theorem denominatorFourGroup_eq (u t : G) :
    denominatorFourGroup u t = Subgroup.zpowers u ⊔ Subgroup.zpowers t := by
  apply le_antisymm
  · change Subgroup.closure ({u, t} : Set G) ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers t
    apply (Subgroup.closure_le _).mpr
    intro s hs
    rcases Set.mem_insert_iff.mp hs with hs | hs
    · rw [hs]
      exact (show Subgroup.zpowers u ≤
        Subgroup.zpowers u ⊔ Subgroup.zpowers t from le_sup_left) (Subgroup.mem_zpowers u)
    · have heq : s = t := hs
      subst s
      exact (show Subgroup.zpowers t ≤
        Subgroup.zpowers u ⊔ Subgroup.zpowers t from le_sup_right) (Subgroup.mem_zpowers t)
  · apply sup_le
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))

variable [Finite G]

theorem four_group_odd_centralizer_generation (J : Subgroup G) (u t : G)
    (hu : orderOf u = 2) (ht : orderOf t = 2) (hut : Commute u t) (hne : u ≠ t)
    (hodd : Odd (Nat.card J))
    (hJN : denominatorFourGroup u t ≤ Subgroup.normalizer (J : Set G)) :
    J = (J ⊓ Subgroup.centralizer ({u} : Set G)) ⊔
      (J ⊓ Subgroup.centralizer ({t} : Set G)) ⊔
      (J ⊓ Subgroup.centralizer ({u * t} : Set G)) := by
  let A := Subgroup.zpowers u ⊔ Subgroup.zpowers t
  obtain ⟨hA, hcard, hcases⟩ := commuting_distinct_involutions_four_group
    hu ht hut (Ne.symm hne)
  have hAN : A ≤ Subgroup.normalizer (J : Set G) := by
    rwa [denominatorFourGroup_eq] at hJN
  apply le_antisymm ?_ (sup_le (sup_le inf_le_left inf_le_left) inf_le_left)
  conv_lhs => rw [← elementary_abelian_centralizer_generation 2 1 Nat.prime_two A J hA
    (by simpa using hcard.ge) hAN (Nat.coprime_two_left.mpr hodd)]
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  have hUcard : Nat.card U = 2 := by simpa using hU.2
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := U) 2
    (by simp only [hUcard, dvd_refl])
  have hsG : orderOf (s : G) = 2 := (Subgroup.orderOf_coe s).trans hs
  have hsne : (s : G) ≠ 1 := by intro heq; simp [heq] at hsG
  have hCs : Subgroup.centralizer (U : Set G) ≤
      Subgroup.centralizer ({(s : G)} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr s.property)
  have hinf : J ⊓ Subgroup.centralizer (U : Set G) ≤
      J ⊓ Subgroup.centralizer ({(s : G)} : Set G) := inf_le_inf_left J hCs
  rcases hcases s (hU.1 s.property) with hone | hu' | ht' | hv'
  · exact False.elim (hsne hone)
  · intro j hj
    have hj' := hinf hj
    rw [hu'] at hj'
    apply (show J ⊓ Subgroup.centralizer ({u} : Set G) ⊔
      J ⊓ Subgroup.centralizer ({t} : Set G) ≤
      (J ⊓ Subgroup.centralizer ({u} : Set G) ⊔
      J ⊓ Subgroup.centralizer ({t} : Set G)) ⊔
      J ⊓ Subgroup.centralizer ({u * t} : Set G) from le_sup_left)
    exact (show J ⊓ Subgroup.centralizer ({u} : Set G) ≤
      (J ⊓ Subgroup.centralizer ({u} : Set G)) ⊔
      (J ⊓ Subgroup.centralizer ({t} : Set G)) from le_sup_left) hj'
  · intro j hj
    have hj' := hinf hj
    rw [ht'] at hj'
    apply (show J ⊓ Subgroup.centralizer ({u} : Set G) ⊔
      J ⊓ Subgroup.centralizer ({t} : Set G) ≤
      (J ⊓ Subgroup.centralizer ({u} : Set G) ⊔
      J ⊓ Subgroup.centralizer ({t} : Set G)) ⊔
      J ⊓ Subgroup.centralizer ({u * t} : Set G) from le_sup_left)
    exact (show J ⊓ Subgroup.centralizer ({t} : Set G) ≤
      (J ⊓ Subgroup.centralizer ({u} : Set G)) ⊔
      (J ⊓ Subgroup.centralizer ({t} : Set G)) from le_sup_right) hj'
  · intro j hj
    have hj' := hinf hj
    rw [hv'] at hj'
    exact (show J ⊓ Subgroup.centralizer ({u * t} : Set G) ≤
      (J ⊓ Subgroup.centralizer ({u} : Set G)) ⊔
      (J ⊓ Subgroup.centralizer ({t} : Set G)) ⊔
      (J ⊓ Subgroup.centralizer ({u * t} : Set G)) from le_sup_right) hj'


end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
