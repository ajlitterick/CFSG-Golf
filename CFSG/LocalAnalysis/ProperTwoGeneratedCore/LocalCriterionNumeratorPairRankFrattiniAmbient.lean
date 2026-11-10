module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairGeneratedHull
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniDimensions

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG LocalCriterionFourGroupCommutator LocalCriterionGeometry
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

@[expose, reducible]
def normalizerFrattiniBaseAction (P : Subgroup G) :
    MulDistribMulAction (Subgroup.normalizer (P : Set G)) P :=
  Subgroup.conjMulDistribMulActionOfLeNormalizer _ P le_rfl


theorem ambient_fixed_subgroup_map (P : Subgroup G) (w : G)
    (hwP : w ∈ Subgroup.normalizer (P : Set G)) :
    let := normalizerFrattiniBaseAction P
    (actorFixedSubgroup (I := P) (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G))).map
      P.subtype = P ⊓ Subgroup.centralizer ({w} : Set G) := by
  let := normalizerFrattiniBaseAction P
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.property, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    change (a : G) * w = w * (a : G)
    have hfix : w * (a : G) * w⁻¹ = a := congrArg Subtype.val ha
    have hm := congrArg (fun y : G => y * w) hfix
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm.symm
  · rintro ⟨hxP, hxw⟩
    refine ⟨⟨x, hxP⟩, ?_, rfl⟩
    apply Subtype.ext
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hxw
    change w * x * w⁻¹ = x
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem ambient_fixed_commutator_map (P : Subgroup G) (w t : G)
    (hwP : w ∈ Subgroup.normalizer (P : Set G))
    (htP : t ∈ Subgroup.normalizer (P : Set G)) (ht : orderOf t = 2) :
    let := normalizerFrattiniBaseAction P
    (actorCommutatorSubgroup (⟨t, htP⟩ : Subgroup.normalizer (P : Set G))
      (actorFixedSubgroup (I := P) (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G)))).map
        P.subtype = rightInvolutionCommutatorSubgroup t
          (P ⊓ Subgroup.centralizer ({w} : Set G)) := by
  let := normalizerFrattiniBaseAction P
  let K := actorCommutatorSubgroup (⟨t, htP⟩ : Subgroup.normalizer (P : Set G))
    (actorFixedSubgroup (I := P) (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G)))
  let C := P ⊓ Subgroup.centralizer ({w} : Set G)
  have htinv : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    apply (actorCommutatorSubgroup_le _ _ _).2
    intro a ha
    have haw : (a : G) ∈ Subgroup.centralizer ({w} : Set G) := by
      have hmap : (a : G) ∈
          (actorFixedSubgroup (I := P) (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G))).map
            P.subtype := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      rw [ambient_fixed_subgroup_map P w hwP] at hmap
      exact hmap.2
    have hright : t⁻¹ * (a : G)⁻¹ * t * a ∈ rightInvolutionCommutatorSubgroup t C :=
      Subgroup.subset_closure ⟨⟨a, a.property, haw⟩, rfl⟩
    have hinv := (rightInvolutionCommutatorSubgroup t C).inv_mem hright
    change (a : G)⁻¹ * (t * (a : G) * t⁻¹) ∈ rightInvolutionCommutatorSubgroup t C
    simpa only [mul_inv_rev, inv_inv, htinv, mul_assoc] using hinv
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨a, rfl⟩
    let aP : P := ⟨a, a.property.1⟩
    have hafix : aP ∈ actorFixedSubgroup (I := P)
        (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G)) := by
      apply Subtype.ext
      change w * (a : G) * w⁻¹ = a
      rw [← Subgroup.mem_centralizer_singleton_iff.mp a.property.2,
        mul_assoc, mul_inv_cancel, mul_one]
    have hgen := actorCommutatorSubgroup_generator_mem
      (⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) hafix
    have himage : ((aP⁻¹ * ((⟨t, htP⟩ : Subgroup.normalizer (P : Set G)) • aP) : P) : G)
        ∈ K.map P.subtype := Subgroup.mem_map.mpr ⟨_, hgen, rfl⟩
    have hinv := (K.map P.subtype).inv_mem himage
    change ((a : G)⁻¹ * (t * (a : G) * t⁻¹))⁻¹ ∈ K.map P.subtype at hinv
    change t⁻¹ * (a : G)⁻¹ * t * a ∈ K.map P.subtype
    simpa only [mul_inv_rev, inv_inv, htinv, mul_assoc] using hinv


end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
