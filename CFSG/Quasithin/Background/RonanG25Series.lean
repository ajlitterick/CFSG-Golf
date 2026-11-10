module

public import CFSG.Quasithin.Background.RonanG25Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.RonanG25

section Series

variable {G : Type} [Group G] {F : Type} [Field F] {X : Subgroup G} {ord : Bool}

theorem FactorNatural.card [Finite G] {A B : Subgroup G} (hAB : A ≤ B)
    (h : FactorNatural F X A B) : Nat.card B = Nat.card F ^ 2 * Nat.card A := by
  obtain ⟨φ, β, hφs, hφk, -, -, -⟩ := h
  have hker : φ.ker = A.subgroupOf B := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφk]
  have hM : Nat.card (Multiplicative (Fin 2 → F)) = Nat.card F ^ 2 := by
    rw [← Nat.card_congr Multiplicative.ofAdd, Nat.card_fun, Nat.card_fin]
  have hrange : Nat.card φ.range = Nat.card F ^ 2 := by
    rw [MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top, hM]
  have h1 := Subgroup.card_mul_index (H := φ.ker)
  rw [Subgroup.index_ker, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv] at h1
  rw [← h1]
  ring


end Series

end CFSG.Quasithin.RonanG25
