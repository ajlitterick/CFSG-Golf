module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Coset and quotient helper lemmas

This file contains auxiliary equivalences and finite-sum decompositions for left
and right cosets. These lemmas are used in the induced-character and double-coset
arguments.
-/

universe u
variable {G : Type u} [Group G]

namespace Subgroup


open Classical in
/--
If a function is constant on every left coset of `H`, then its sum over `G` is
the sum over left cosets multiplied by `|H|`.

This is the left-coset analogue of `Subgroup.sum_of_right_coset_constant`.
-/
lemma sum_of_left_coset_constant {k : Type*} [Semiring k] [Fintype G]
    (H : Subgroup G) (f : G → k)
    (h_const : ∀ (x : G) (h : H), f (x * (h : G)) = f x) :
    ∑ x : G, f x = (Nat.card H : k) * ∑ q : G ⧸ H, f q.out := by
  let π : G → G ⧸ H := Quotient.mk _
  rw [← Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ (π x)) f]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  let fiber := {x : G // π x = q}
  -- The core bijection between a left coset fiber and the subgroup H
  let e : fiber ≃ H :=
  { toFun := fun x => ⟨q.out⁻¹ * x.1, by
      have h_eq : ⟦q.out⟧ = ⟦x.1⟧ :=
        calc ⟦q.out⟧ = q := Quotient.out_eq q
             _ = ⟦x.1⟧ := x.property.symm
      exact QuotientGroup.eq.mp h_eq⟩
    invFun := fun h => ⟨q.out * (h : G), by
      change ⟦q.out * (h : G)⟧ = q
      rw [← Quotient.out_eq q, QuotientGroup.eq]
      simp only [Quotient.out_eq, mul_inv_rev, inv_mul_cancel_right, inv_mem_iff, SetLike.coe_mem]⟩
    left_inv := fun x => Subtype.ext (by dsimp; group)
    right_inv := fun h => Subtype.ext (by dsimp; group) }
  have h_inner_const : ∀ x : fiber, f x.1 = f q.out := by
    intro x
    let h : H := e x
    have hx : q.out * (h : G) = x.1 := congrArg Subtype.val (e.left_inv x)
    have h_eq := h_const q.out h
    rw [hx] at h_eq
    exact h_eq
  rw [Finset.sum_congr rfl (fun x hx => h_inner_const ⟨x, (Finset.mem_filter.mp hx).2⟩)]
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [← Fintype.card_coe, ← Fintype.card_eq_nat_card]
  exact congrArg (fun n : ℕ => (n : k)) (by simpa [fiber] using Fintype.card_congr e)

end Subgroup

namespace QuotientGroup


end QuotientGroup
