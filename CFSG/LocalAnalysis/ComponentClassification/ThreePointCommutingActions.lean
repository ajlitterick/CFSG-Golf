module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open scoped Pointwise

namespace CFSG.ComponentClassification.ThreePointCommutingActions

theorem unique_fixed (swap : Equiv.Perm (Fin 3))
    (hswap : swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2) :
    ∃ fixed : Fin 3, ∀ point : Fin 3, swap point = point ↔ point = fixed := by
  have hfinite : ∀ swap : Equiv.Perm (Fin 3),
      (swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2) →
      ∃ fixed : Fin 3, ∀ point : Fin 3, swap point = point ↔ point = fixed := by decide
  exact hfinite swap hswap


theorem involution_swap (permutation : Equiv.Perm (Fin 3))
    (hsquare : permutation ^ 2 = 1) (hne : permutation ≠ 1) :
    permutation = Equiv.swap 0 1 ∨ permutation = Equiv.swap 0 2 ∨ permutation = Equiv.swap 1 2 := by
  have hfinite : ∀ permutation : Equiv.Perm (Fin 3), permutation ^ 2 = 1 → permutation ≠ 1 →
      permutation = Equiv.swap 0 1 ∨ permutation = Equiv.swap 0 2 ∨ permutation = Equiv.swap 1 2 := by decide
  exact hfinite permutation hsquare hne


theorem swap_mem (subgroup : Subgroup (Equiv.Perm (Fin 3))) (heven : Even (Nat.card subgroup)) :
    ∃ swap ∈ subgroup, swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2 := by
  obtain ⟨member, horder⟩ := exists_prime_orderOf_dvd_card' (G := subgroup) 2 (even_iff_two_dvd.mp heven)
  have horderAmbient : orderOf member.val = 2 :=
    (orderOf_injective subgroup.subtype subgroup.subtype_injective member).trans horder
  have hsquare : member.val ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (horderAmbient ▸ dvd_rfl)
  have hne : member.val ≠ 1 := by
    intro hone
    rw [hone, orderOf_one] at horderAmbient
    omega
  exact ⟨member.val, member.property, involution_swap member.val hsquare hne⟩


end CFSG.ComponentClassification.ThreePointCommutingActions
