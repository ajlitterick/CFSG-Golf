module

public import CFSG.ClassicalInvolution.Balance.BootstrapAuditFamily
public import CFSG.ClassicalInvolution.Balance.LayerGenerationLie

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure


section Abstract

variable {X : Type} [Group X]

theorem commute_of_mem_closure {S : Set X} (h : ∀ z ∈ S, ∀ w ∈ S, z * w = w * z) {x y : X}
    (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure S) : Commute x y := by
  have h1 : ∀ z ∈ S, ∀ y ∈ Subgroup.closure S, Commute z y := by
    intro z hz y hy
    induction hy using Subgroup.closure_induction with
    | mem w hw => exact h z hz w hw
    | one => exact Commute.one_right z
    | mul a b _ _ iha ihb => exact iha.mul_right ihb
    | inv a _ iha => exact iha.inv_right
  induction hx using Subgroup.closure_induction with
  | mem z hz => exact h1 z hz y hy
  | one => exact Commute.one_left y
  | mul a b _ _ iha ihb => exact iha.mul_left ihb
  | inv a _ iha => exact iha.inv_left

theorem mul_self_eq_one_of_mem_closure {S : Set X} (h2 : ∀ z ∈ S, z * z = 1)
    (h : ∀ z ∈ S, ∀ w ∈ S, z * w = w * z) {x : X} (hx : x ∈ Subgroup.closure S) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem z hz => exact h2 z hz
  | one => exact mul_one 1
  | mul a b ha hb iha ihb =>
    have hab : Commute a b := commute_of_mem_closure h ha hb
    calc a * b * (a * b) = a * a * (b * b) := by
          rw [mul_assoc, ← mul_assoc b a b, hab.symm.eq, mul_assoc a b b, ← mul_assoc]
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a _ iha => rw [← mul_inv_rev, iha, inv_one]


end Abstract

section Local


end Local

section Providers


end Providers

section KG8


end KG8

end CFSG.ClassicalInvolution.Balance.Bootstrap
