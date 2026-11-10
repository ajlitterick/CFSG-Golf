module

public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionNormalizer
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentActionBasic

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]


theorem inf_eq_bot_of_isPGroup_of_coprime {p : ℕ} [Fact p.Prime] [Finite G] {P N : Subgroup G}
    (hP : IsPGroup p P) (hN : ¬ p ∣ Nat.card N) : P ⊓ N = ⊥ := by
  have hPN : IsPGroup p (P ⊓ N : Subgroup G) := hP.to_le inf_le_left
  obtain ⟨k, hk⟩ := hPN.exists_card_eq
  have hdvd : Nat.card (P ⊓ N : Subgroup G) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le inf_le_right
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  · exfalso
    apply hN
    rw [hk] at hdvd
    exact (dvd_pow_self p (Nat.succ_ne_zero k)).trans hdvd


end CFSG.ComponentClassification.AschbacherToolkit
