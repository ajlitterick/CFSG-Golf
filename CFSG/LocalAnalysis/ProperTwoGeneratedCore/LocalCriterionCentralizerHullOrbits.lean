module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingConjugacy

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

theorem entire_point_involution_root_normalized
    (P U : Subgroup G)
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ P ∧ IsInvolution x}) :
    P ≤ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro p hp x hx
  change x ∈ (U : Set G) at hx
  change p * x * p⁻¹ ∈ (U : Set G)
  rw [hU] at hx ⊢
  rcases hx with hx | hx
  · have hxone := Set.mem_singleton_iff.mp hx
    subst x
    exact Or.inl (by simp)
  · refine Or.inr ⟨P.mul_mem (P.mul_mem hp hx.1) (P.inv_mem hp), ?_⟩
    have h := isInvolution_rightConjugateElem (g := p⁻¹) hx.2
    simpa only [rightConjugateElem, inv_inv] using h

theorem entire_point_root_conjugacy_class [Finite G]
    (L P U : Subgroup G) (hPL : P ≤ L)
    (hP : IsStronglyEmbedded (P.subgroupOf L))
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ P ∧ IsInvolution x})
    (z : G) (hzP : z ∈ P) (hz : IsInvolution z) :
    conjugacyWithin P z = (U : Set G) \ {1} := by
  ext x
  constructor
  · rintro ⟨p, hpx⟩
    have hxP : x ∈ P := hpx ▸ P.mul_mem (P.mul_mem (P.inv_mem p.property) hzP) p.property
    have hx : IsInvolution x := hpx ▸ isInvolution_rightConjugateElem hz
    refine ⟨?_, hx.ne_one⟩
    rw [hU]
    exact Or.inr ⟨hxP, hx⟩
  · rintro ⟨hxU, hxone⟩
    rw [hU] at hxU
    rcases hxU with hx | hx
    · exact (hxone hx).elim
    · have hzL : z ∈ L := hPL hzP
      have hxL : x ∈ L := hPL hx.1
      obtain ⟨p, hp, hpx⟩ := hP.involutions_conjugate_in
        (a := (⟨z, hzL⟩ : L)) (b := (⟨x, hxL⟩ : L))
        hzP (IsInvolution.subtype hz hzL) hx.1 (IsInvolution.subtype hx.2 hxL)
      exact ⟨⟨p, hp⟩, congrArg Subtype.val hpx⟩

theorem entire_hull_involution_conjugacy_class [Finite G]
    (L P : Subgroup G) (hP : IsStronglyEmbedded (P.subgroupOf L))
    (z : G) (hzL : z ∈ L) (hz : IsInvolution z) :
    conjugacyWithin L z = {x : G | x ∈ L ∧ IsInvolution x} := by
  ext x
  constructor
  · rintro ⟨l, hlx⟩
    exact ⟨hlx ▸ L.mul_mem (L.mul_mem (L.inv_mem l.property) hzL) l.property,
      hlx ▸ isInvolution_rightConjugateElem hz⟩
  · rintro ⟨hxL, hx⟩
    obtain ⟨l, hlx⟩ := hP.involutions_conjugate
      (IsInvolution.subtype hz hzL) (IsInvolution.subtype hx hxL)
    exact ⟨l, congrArg Subtype.val hlx⟩

theorem entire_normalizer_root_conjugacy_class
    (L P U : Subgroup G) (hPL : P ≤ L)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (z : G) (hzU : z ∈ U) (hz : z ≠ 1)
    (hPclass : conjugacyWithin P z = (U : Set G) \ {1}) :
    conjugacyWithin (L ⊓ Subgroup.normalizer (U : Set G)) z = (U : Set G) \ {1} := by
  ext x
  constructor
  · rintro ⟨n, hnx⟩
    have hxU : x ∈ U := hnx ▸
      (Subgroup.mem_normalizer_iff''.mp n.property.2 z).mp hzU
    refine ⟨hxU, ?_⟩
    intro hxone
    apply hz
    have h := congrArg (fun y : G => (n : G) * y * (n : G)⁻¹) (hnx.trans hxone)
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel,
      one_mul, mul_one] using h
  · intro hx
    obtain ⟨p, hpx⟩ := Set.ext_iff.mp hPclass x |>.mpr hx
    exact ⟨⟨p, hPL p.property, hPU p.property⟩, hpx⟩


theorem conjugation_orbit_eq_conjugacyWithin (A : Subgroup G) (x : G) :
    let _ : MulAction A G := MulAction.compHom G
      (ConjAct.toConjAct.toMonoidHom.comp A.subtype)
    MulAction.orbit A x = conjugacyWithin A x := by
  let _ : MulAction A G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp A.subtype)
  ext y
  constructor
  · rintro ⟨a, hay⟩
    refine ⟨a⁻¹, ?_⟩
    change (a : G) * x * (a : G)⁻¹ = y at hay
    simpa only [Subgroup.coe_inv, inv_inv] using hay
  · rintro ⟨a, hay⟩
    refine ⟨a⁻¹, ?_⟩
    change (a : G)⁻¹ * x * (a : G)⁻¹⁻¹ = y
    simpa only [inv_inv] using hay


end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
