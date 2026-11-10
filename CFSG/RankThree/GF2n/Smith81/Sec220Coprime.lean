module

public import CFSG.GroupTheory.SolvableHallNodes
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.GF2n.Smith81

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem eq_one_of_mem_of_orderOf_dvd_odd {P : Subgroup G} (hP : IsPGroup 2 P) {x : G}
    (hx : x ∈ P) {m : ℕ} (hm : Odd m) (hdvd : orderOf x ∣ m) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have h1 : orderOf x ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_two_right.mpr (hm.of_dvd_nat hdvd)))
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)


end CFSG.RankThree.GF2n.Smith81
