module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearLagrangian
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearOuterInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamilies

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_linear_all_involution_centralizer_exceptions)
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)

section Model

variable {n : ℕ} {K : Type} [Field K]

theorem oddCore_projectiveSL_inf_centralizer_eq_bot {f : ℕ} (hn : 4 ≤ n)
    (hK : Nat.card K = 2 ^ f) (H : Subgroup (MulAut (projectiveSL n K)))
    (hIH : inner (projectiveSL n K) ≤ H) {α : MulAut (projectiveSL n K)} (hα : orderOf α = 2) :
    CFSG.oddCore ↥(H ⊓ centralizer ({α} : Set (MulAut (projectiveSL n K)))) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact hf
  by_contra hne
  obtain ⟨h3, -⟩ := even_linear_all_involution_centralizer_exceptions (by omega) hf hK hIH hα hne
  rcases h3 with ⟨h3, -⟩ | ⟨h3, -⟩ <;> omega

theorem involutionCriterion_projectiveSL {f : ℕ} (hn : 4 ≤ n) (hK : Nat.card K = 2 ^ f)
    (hnf : ¬(n = 4 ∧ f = 1)) {x : MulAut (projectiveSL n K)} (hx : orderOf x = 2) :
    InvolutionCriterion x := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact hf
  by_cases hxI : x ∈ inner (projectiveSL n K)
  · exact ClassicalLinear.involutionCriterion_of_mem_inner hn hf hK hnf hxI hx
  · exact LinearOuter.involutionCriterion_of_not_mem_range_conj hf hK hn hnf hxI
      (by rw [← hx]; exact pow_orderOf_eq_one x)

theorem hypothesisOne_projectiveSL {f : ℕ} (hn : 4 ≤ n) (hK : Nat.card K = 2 ^ f)
    (hnf : ¬(n = 4 ∧ f = 1)) : HypothesisOne (projectiveSL n K) :=
  hypothesisOne_of_involutionCriterion
    (CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (by omega))
    (fun H hIH _ _ hα => oddCore_projectiveSL_inf_centralizer_eq_bot hn hK H hIH hα)
    (fun _ hx => involutionCriterion_projectiveSL hn hK hnf hx)

end Model


end CFSG.SeitzReduction
