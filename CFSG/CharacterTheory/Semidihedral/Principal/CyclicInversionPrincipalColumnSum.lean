module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive

public section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u

namespace CyclicColumnSum

open Equiv

section Sylow

variable {H : Type u} [Group H]

theorem centralizer_eq (W P : Subgroup H) (hPW : P ≤ W) (hodd : Odd (Nat.card W))
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hP1 : P ≠ ⊥) :
    Subgroup.centralizer (P : Set H) = Subgroup.centralizer (W : Set H) := by
  apply le_antisymm
  · intro h hh
    by_contra hhW
    apply hP1
    rw [eq_bot_iff]
    intro p hp
    have h1 := hinv h hhW p (hPW hp)
    have h2 : h * p * h⁻¹ = p := by
      rw [← Subgroup.mem_centralizer_iff.mp hh p hp, mul_inv_cancel_right]
    rw [h2] at h1
    have hp2 : p ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [h1]
      exact mul_inv_cancel p
    exact Subgroup.mem_bot.mpr (CyclicSymmetricFour.eq_one_of_sq_eq_one W hodd (hPW hp) hp2)
  · exact Subgroup.centralizer_le fun x hx => hPW hx

end Sylow

section Sums

open scoped Classical


end Sums

section Core

open scoped Classical


end Core

end CyclicColumnSum

open CyclicColumnSum


end CFSG.Semidihedral.Principal
