module

public import CFSG.Quasithin.Background.D36GluedL3Fin
import CFSG.ClassicalInvolution.Q3.TL4D1ML32B
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Quasithin.L3Mod

open CFSG.Quasithin.L3 CFSG.Quasithin.L3Fin


inductive Attain : ℕ → Prop
  | zero : Attain 0
  | add {n d : ℕ} : Attain n → d ∣ 168 → 7 ≤ d → Attain (n + d)

theorem Attain.small {n : ℕ} (h : Attain n) (h17 : n ≤ 17) :
    n = 0 ∨ n = 7 ∨ n = 8 ∨ n = 12 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
  induction h with
  | zero => exact Or.inl rfl
  | @add n d _ hd h7 ih =>
    have hn := ih (by omega)
    have hd17 : d ≤ 17 := by omega
    have hd' : d = 7 ∨ d = 8 ∨ d = 12 ∨ d = 14 := by
      interval_cases d <;> omega
    omega

section Action

variable {M : Type} [CommGroup M] [Finite M] [MulDistribMulAction Γ M]


end Action


structure Datum where
  H₁ : Subgroup Γ
  H₂ : Subgroup Γ
  hs : Fin 3 → Γ
  card₁ : Nat.card H₁ = 24
  card₂ : Nat.card H₂ = 24
  hs_zero : hs 0 = 1
  two_trans : ∀ g : Γ, g ∈ H₁ ∨ ∃ a ∈ H₁, (hs 1)⁻¹ * (a⁻¹ * g) ∈ H₁
  distinct : ∀ i j : Fin 3, (hs i)⁻¹ * hs j ∈ H₁ → i = j
  closed : ∀ q ∈ H₂, ∀ i : Fin 3, ∃ j : Fin 3, (hs j)⁻¹ * (q * hs i) ∈ H₁
  not_conj : ∀ g : Γ, ∃ a ∈ H₁, g * a * g⁻¹ ∉ H₂

def Datum.P : Datum where
  H₁ := subP
  H₂ := subQ
  hs := hsP
  card₁ := card_subP
  card₂ := card_subQ
  hs_zero := hsP_zero
  two_trans := P_two_trans
  distinct := P_distinct
  closed := fun q hq => P_closed q hq
  not_conj := fun g => by
    obtain ⟨a, ha, h⟩ := P_not_conj g
    exact ⟨a, ha, h⟩

def Datum.Q : Datum where
  H₁ := subQ
  H₂ := subP
  hs := hsQ
  card₁ := card_subQ
  card₂ := card_subP
  hs_zero := hsQ_zero
  two_trans := Q_two_trans
  distinct := Q_distinct
  closed := fun q hq => Q_closed q hq
  not_conj := fun g => by
    obtain ⟨a, ha, h⟩ := Q_not_conj g
    exact ⟨a, ha, h⟩

section Fano


end Fano

end CFSG.Quasithin.L3Mod
