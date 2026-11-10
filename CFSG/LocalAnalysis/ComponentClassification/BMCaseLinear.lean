module

public import CFSG.LinearAlgebra.IrreducibleBinaryCentralizerField
public import Mathlib.GroupTheory.PGroup

public noncomputable section

namespace CFSG.ComponentClassification.BMCase

open Subgroup Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]


theorem pow_three_eq_one_of_orderOf_dvd {G : Type*} [Monoid G] {a : G} {d : ℕ} (hd : 0 < d)
    (hd2 : d ≤ 2) (ha : orderOf a ∣ 2 ^ d - 1) : a ^ 3 = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.1
  interval_cases d
  · exact ha.trans (by norm_num)
  · exact ha

variable [FiniteDimensional (ZMod 2) V]


theorem finite_generalLinearGroup : Finite (LinearMap.GeneralLinearGroup (ZMod 2) V) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V →ₗ[ZMod 2] V) := Finite.of_injective _ DFunLike.coe_injective
  infer_instance

theorem pow_three_eq_one_of_dim_twentytwo (hV : finrank (ZMod 2) V = 22)
    (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ h ∈ H, ∀ w ∈ W, (h : V →ₗ[ZMod 2] V) w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h2 : 2 ^ 18 ∣ Nat.card H) (a : LinearMap.GeneralLinearGroup (ZMod 2) V)
    (ha : a ∈ centralizer (H : Set (LinearMap.GeneralLinearGroup (ZMod 2) V))) : a ^ 3 = 1 := by
  obtain ⟨-, d, hd0, hd, -, hord, -, h2part⟩ :=
    CFSG.LinearAlgebra.irreducible_binary_linear_centralizer_field_degree_bound (by norm_num) hV
      H hirr a ha
  refine pow_three_eq_one_of_orderOf_dvd hd0 ?_ hord
  by_contra hlt
  push Not at hlt
  have := finite_generalLinearGroup (V := V)
  have hH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h18 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hH0).1 h2
  have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 h2part
  have hd' : d ≤ 22 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> omega


end CFSG.ComponentClassification.BMCase
