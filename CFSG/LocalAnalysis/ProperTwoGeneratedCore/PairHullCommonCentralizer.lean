module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherEscapingRankTwo
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

public section

namespace CFSG.ProperTwoGeneratedCore.PairHullCommonCentralizer

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.BenderSuzuki.PFAppendixIII CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

variable {G : Type} [Group G]


theorem conj_mem_localHull_of_commute {z w x c : G} (hc : Commute c w)
    (hx : x ∈ localInvolutionPointHull z w) :
    c⁻¹ * x * c ∈ localInvolutionPointHull z w := by
  have h := conj_mem_localInvolutionPointHull (z := z) c hx
  have hw : c⁻¹ * w * c = w := by
    rw [mul_assoc, ← hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  rwa [hw] at h

theorem commutator_centralizer_le_localHull {z w t : G} (I : Subgroup G)
    (ht : t ∈ localInvolutionPointHull z w) :
    ⁅I ⊓ Subgroup.centralizer {w}, Subgroup.zpowers t⁆ ≤ localInvolutionPointHull z w := by
  rw [Subgroup.commutator_le]
  intro c hc k hk
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  have hcw : Commute c w :=
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2)
  have htn : t ^ n ∈ localInvolutionPointHull z w := Subgroup.zpow_mem _ ht n
  have hconj : c * t ^ n * c⁻¹ ∈ localInvolutionPointHull z w := by
    have := conj_mem_localHull_of_commute (z := z) (c := c⁻¹) hcw.inv_left htn
    simpa only [inv_inv] using this
  exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ htn)


end CFSG.ProperTwoGeneratedCore.PairHullCommonCentralizer
