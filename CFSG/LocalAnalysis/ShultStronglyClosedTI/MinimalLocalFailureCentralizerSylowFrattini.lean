module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaIndex
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CentralizerSylow

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem full_point_centralizer_normal
    (A X : Subgroup G) (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    ((A ⊓ Subgroup.centralizer (X : Set G)).subgroupOf A).Normal := by
  let C := Subgroup.centralizer (X : Set G)
  let Y := Subgroup.normalizer (X : Set G)
  have hCY : C ≤ Y := Subgroup.centralizer_le_normalizer _
  have hYC : Y ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCY).mp
      (inferInstance : (C.subgroupOf Y).Normal)
  have hAC : A ≤ Subgroup.normalizer (A ⊓ C : Set G) :=
    (le_inf A.le_normalizer (hAX.trans hYC)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact Subgroup.normal_subgroupOf_of_le_normalizer hAC


theorem odd_normal_sylow_normalizer_even
    (D : Subgroup G) [D.Normal] (hDodd : Odd (Nat.card D))
    (heven : Even (Nat.card G)) (p : ℕ) (hp : p.Prime) (P : Sylow p D) :
    Even (Nat.card (Subgroup.normalizer
      (((P : Subgroup D).map D.subtype : Subgroup G) : Set G))) := by
  let : Fact p.Prime := ⟨hp⟩
  let N := Subgroup.normalizer (((P : Subgroup D).map D.subtype : Subgroup G) : Set G)
  have hgen : D ⊔ N = ⊤ := by
    rw [sup_comm]
    exact P.normalizer_sup_eq_top
  have hindexodd : Odd N.index := hDodd.of_dvd_nat (by
    rw [← Subgroup.relIndex_top_right N, ← hgen, sup_comm D N,
      LocalTheta.normal_factor_relative_index D N]
    exact N.relIndex_dvd_card D)
  apply Nat.not_odd_iff_even.mp
  intro hNodd
  have hGodd : Odd (Nat.card G) := by
    rw [← N.card_mul_index]
    exact hNodd.mul hindexodd
  exact (Nat.not_even_iff_odd.mpr hGodd) heven


end CFSG.ShultStronglyClosedTI.CentralizerSylow
