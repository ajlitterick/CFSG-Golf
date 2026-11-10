module

public import CFSG.Certificates.Kernel.E7Orbit.Sound

public section

namespace CFSG.KC.E7Orbit

open Equiv CFSG.KC.Benes
open scoped Pointwise

variable {T NT RT : Nat → Nat}

theorem msk_lt (hN : ∀ i < 3159, nodeOK T NT RT i = true) {i : Nat} (hi : i < 3159) :
    msk (recAt T i) < 2 ^ 2187 :=
  (nodeOK_sound (hN i hi)).1


theorem msk_strict (hN : ∀ i < 3159, nodeOK T NT RT i = true) {i : Nat} :
    ∀ {j : Nat}, i < j → j < 3159 → msk (recAt T i) < msk (recAt T j)
  | 0, h, _ => absurd h (Nat.not_lt_zero i)
  | j + 1, h, hj => by
    have hs := (nodeOK_sound (hN j (by omega))).2.1 hj
    rcases Nat.lt_or_ge i j with h2 | h2
    · exact lt_trans (msk_strict hN h2 (by omega)) hs
    · have e : i = j := by omega
      subst e
      exact hs

theorem maskSet_inj {M M' : Nat} (h : M < 2 ^ 2187) (h' : M' < 2 ^ 2187)
    (e : maskSet M = maskSet M') : M = M' := by
  apply Nat.eq_of_testBit_eq
  intro q
  rcases Nat.lt_or_ge q 2187 with hq | hq
  · have := congrArg (fun S => (⟨q, hq⟩ : Fin 2187) ∈ S) e
    simp only [maskSet, Set.mem_setOf_eq, eq_iff_iff] at this
    exact Bool.eq_iff_iff.2 this
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hq)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h' (Nat.pow_le_pow_right (by decide) hq))]

theorem nodes_inj (hN : ∀ i < 3159, nodeOK T NT RT i = true) {i j : Nat} (hi : i < 3159)
    (hj : j < 3159) (e : maskSet (msk (recAt T i)) = maskSet (msk (recAt T j))) : i = j := by
  have he := maskSet_inj (msk_lt hN hi) (msk_lt hN hj) e
  rcases Nat.lt_trichotomy i j with h | h | h
  · have := msk_strict hN h hj
    rw [he] at this
    exact absurd this (lt_irrefl _)
  · exact h
  · have := msk_strict hN h hi
    rw [he] at this
    exact absurd this (lt_irrefl _)

end CFSG.KC.E7Orbit

end
