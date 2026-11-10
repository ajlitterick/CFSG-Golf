module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullFixedSet
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorRightOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G]

theorem elementFixedSet_conjugate_image (H : Subgroup G) (u g : G) :
    (fun a => pointRightCosetMul H a g) '' elementFixedSet H u =
      elementFixedSet H (rightConjugateElem u g) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (elementFixedSetConjugateEquiv H u g ⟨b, hb⟩).property
  · intro ha
    refine ⟨pointRightCosetMul H a g⁻¹,
      (elementFixedSet_conjugate_iff H u g a).mp ha, ?_⟩
    change pointRightCosetMul H (pointRightCosetMul H a g⁻¹) g = a
    rw [pointRightCosetMul_mul, inv_mul_cancel, pointRightCosetMul_one]

theorem right_orbit_conjugate_image (H L : Subgroup G)
    (a : pointRightCosetSpace H) (g : G) :
    (fun x => pointRightCosetMul H x g) '' numeratorRightOrbit H L a =
      numeratorRightOrbit H (L.map (MulAut.conj g⁻¹).toMonoidHom)
        (pointRightCosetMul H a g) := by
  ext x
  constructor
  · rintro ⟨y, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨rightConjugateElem l g, Subgroup.mem_map.mpr ⟨l, hl, ?_⟩, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, rightConjugateElem]
    · exact (right_coset_conjugate_intertwines H a l g).symm
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨k, hk, heq⟩ := Subgroup.mem_map.mp hl
    have heq' : rightConjugateElem k g = l := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, rightConjugateElem] using heq
    refine ⟨pointRightCosetMul H a k, ⟨k, hk, rfl⟩, ?_⟩
    rw [← heq']
    exact right_coset_conjugate_intertwines H a k g

theorem conjugate_hull_full_fixedSet_orbit (H : Subgroup G) (z u g : G)
    (a : pointRightCosetSpace H)
    (hfull : elementFixedSet H u = numeratorRightOrbit H (localInvolutionPointHull z u) a) :
    elementFixedSet H (rightConjugateElem u g) =
      numeratorRightOrbit H (localInvolutionPointHull z (rightConjugateElem u g))
        (pointRightCosetMul H a g) := by
  rw [← elementFixedSet_conjugate_image, hfull, right_orbit_conjugate_image,
    local_hull_conjugate_map]


end CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
