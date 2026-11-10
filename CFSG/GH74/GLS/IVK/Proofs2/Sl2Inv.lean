module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Sl2Inv

open Matrix

variable {F : Type*} [Field F]

@[expose] def upper (a : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] lemma coe_upper (a : F) : (upper a : Matrix (Fin 2) (Fin 2) F) = !![1, a; 0, 1] := rfl


lemma card_SL2 [Finite F] :
    Nat.card (SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, Fin.prod_univ_two]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  generalize Nat.card F = q at hq ⊢
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  apply Nat.div_eq_of_eq_mul_left (by omega)
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : q ≤ q ^ 2 := by nlinarith
  zify [h1, h2, (by omega : 1 ≤ q)]
  ring

lemma factorization_card_SL2 [Finite F] {p n : ℕ} (hp : p.Prime) (hq : Nat.card F = p ^ n) :
    (Nat.card (SpecialLinearGroup (Fin 2) F)).factorization p = n := by
  have hn : n ≠ 0 := by
    rintro rfl
    have : 1 < Nat.card F := Finite.one_lt_card
    simp [hq] at this
  have hpq : p ∣ Nat.card F := by rw [hq]; exact dvd_pow_self p hn
  have hq0 : Nat.card F ≠ 0 := Nat.card_pos.ne'
  have hnd : ¬ p ∣ Nat.card F ^ 2 - 1 := by
    intro h
    have h2 : p ∣ Nat.card F ^ 2 := dvd_pow hpq two_ne_zero
    have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    have := Nat.dvd_sub h2 h
    rw [Nat.sub_sub_self h1] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hne : Nat.card F ^ 2 - 1 ≠ 0 := by
    have : 1 < Nat.card F := Finite.one_lt_card
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow two_ne_zero this
    omega
  rw [card_SL2, Nat.factorization_mul hq0 hne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, add_zero, hq, hp.factorization_pow,
    Finsupp.single_eq_same]


end Sl2Inv


end CFSG.GH74.GLS.IVK.Proofs2
