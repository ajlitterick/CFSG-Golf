module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.KC.PCent

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem card_mul_card_stab_le {α : Type*} [MulAction G α] {H : Subgroup G} [Finite H] {x : α}
    (S : Finset α) (hS : ∀ s ∈ S, ∃ g ∈ H, g • x = s) :
    S.card * Nat.card (H ⊓ MulAction.stabilizer G x : Subgroup G) ≤ Nat.card H := by
  classical
  choose! f hfH hfx using hS
  let F : S × (H ⊓ MulAction.stabilizer G x : Subgroup G) → H := fun p =>
    ⟨f p.1 * p.2, H.mul_mem (hfH _ p.1.2) (Subgroup.mem_inf.1 p.2.2).1⟩
  have hF : Function.Injective F := by
    rintro ⟨⟨s, hs⟩, ⟨c, hc⟩⟩ ⟨⟨t, ht⟩, ⟨d, hd⟩⟩ h
    have h' : f s * c = f t * d := congrArg Subtype.val h
    have hcx : c • x = x := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hc).2
    have hdx : d • x = x := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hd).2
    have hst : s = t := by
      have e := congrArg (· • x) h'
      simp only [mul_smul, hcx, hdx] at e
      rw [← hfx s hs, ← hfx t ht]
      exact e
    subst hst
    have hcd : c = d := mul_left_cancel h'
    subst hcd
    rfl
  have hle := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_finsetCard] at hle

theorem card_mul_card_centralizer_le {H : Subgroup G} [Finite H] {v : G} (S : Finset G)
    (hS : ∀ s ∈ S, ∃ g ∈ H, g * v * g⁻¹ = s) :
    S.card * Nat.card (H ⊓ Subgroup.centralizer {v} : Subgroup G) ≤ Nat.card H := by
  classical
  choose! f hfH hfx using hS
  have key : ∀ a c : G, c ∈ Subgroup.centralizer {v} → a * c * v * (a * c)⁻¹ = a * v * a⁻¹ := by
    intro a c hc
    have hcv : v * c = c * v := Subgroup.mem_centralizer_iff.1 hc v (Set.mem_singleton v)
    have e : c * v * c⁻¹ = v := by rw [← hcv, mul_inv_cancel_right]
    calc a * c * v * (a * c)⁻¹ = a * (c * v * c⁻¹) * a⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = a * v * a⁻¹ := by rw [e]
  let F : S × (H ⊓ Subgroup.centralizer {v} : Subgroup G) → H := fun p =>
    ⟨f p.1 * p.2, H.mul_mem (hfH _ p.1.2) (Subgroup.mem_inf.1 p.2.2).1⟩
  have hF : Function.Injective F := by
    rintro ⟨⟨s, hs⟩, ⟨c, hc⟩⟩ ⟨⟨t, ht⟩, ⟨d, hd⟩⟩ h
    have h' : f s * c = f t * d := congrArg Subtype.val h
    have hst : s = t := by
      have e := congrArg (fun y => y * v * y⁻¹) h'
      rw [key _ _ (Subgroup.mem_inf.1 hc).2, key _ _ (Subgroup.mem_inf.1 hd).2, hfx s hs,
        hfx t ht] at e
      exact e
    subst hst
    have hcd : c = d := mul_left_cancel h'
    subst hcd
    rfl
  have hle := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_finsetCard] at hle


end CFSG.KC.PCent

end
