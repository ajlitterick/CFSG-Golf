module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ClassicalInvolution.Q3

open scoped Pointwise commutatorElement

section Sylow


end Sylow

section Abstract

variable {C : Type*} [Group C] {A : Type*} [Group A]

@[expose] def centModO (ρ : C →* A) (O : Subgroup C) [O.Normal] : Subgroup C where
  carrier := {w | ∀ y ∈ ρ.ker, ⁅w, y⁆ ∈ O}
  one_mem' := fun y _ => by simp [O.one_mem]
  mul_mem' {a b} ha hb y hy := by
    have h1 : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact O.mul_mem (Subgroup.Normal.conj_mem inferInstance _ (hb y hy) a) (ha y hy)
  inv_mem' {a} ha y hy := by
    have h1 : ⁅a⁻¹, y⁆ = a⁻¹ * (⁅a, y⁆)⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [h1]
    have h2 := Subgroup.Normal.conj_mem (inferInstance : O.Normal) _ (O.inv_mem (ha y hy)) a⁻¹
    simpa using h2


end Abstract

section Equiv

variable {C : Type*} [Group C] [Finite C] {A : Type*} [Group A]

theorem exists_centModO_of_inner (ρ : C →* A) (O : Subgroup C) [O.Normal] {x : C}
    (hx3 : ρ x ^ 3 = 1) (hx1 : ρ x ≠ 1)
    (hin : ∃ dd ∈ ρ.ker, ∀ y ∈ ρ.ker, x * y * x⁻¹ * (dd * y * dd⁻¹)⁻¹ ∈ O) :
    ∃ (x' : C) (k' : ℕ), x' ^ 3 ^ k' = 1 ∧ ρ x' ≠ 1 ∧ x' ∈ centModO ρ O := by
  obtain ⟨dd, hdd, hy⟩ := hin
  have hwO : dd⁻¹ * x ∈ centModO ρ O := by
    intro y hy'
    have h1 : ⁅dd⁻¹ * x, y⁆ = dd⁻¹ * (x * y * x⁻¹ * (dd * y * dd⁻¹)⁻¹) * dd := by
      simp only [commutatorElement_def]; group
    rw [h1]
    have := Subgroup.Normal.conj_mem (inferInstance : O.Normal) _ (hy y hy') dd⁻¹
    simpa using this
  have hρw : ρ (dd⁻¹ * x) = ρ x := by
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp hdd, inv_one, one_mul]
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (dd⁻¹ * x)).ne' 3
    (by norm_num)
  refine ⟨(dd⁻¹ * x) ^ (b * b), a, ?_, ?_, Subgroup.pow_mem _ hwO _⟩
  · rw [← pow_mul]
    have : b * b * 3 ^ a = orderOf (dd⁻¹ * x) * b := by rw [hab]; ring
    rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
  · rw [map_pow, hρw]
    have hord : orderOf (ρ x) = 3 := orderOf_eq_prime hx3 hx1
    have hb3 : b % 3 = 1 ∨ b % 3 = 2 := by omega
    have hbb : (b * b) % 3 = 1 := by rcases hb3 with h | h <;> simp [Nat.mul_mod, h]
    rw [← pow_mod_orderOf, hord, hbb, pow_one]
    exact hx1


end Equiv

end CFSG.ClassicalInvolution.Q3
