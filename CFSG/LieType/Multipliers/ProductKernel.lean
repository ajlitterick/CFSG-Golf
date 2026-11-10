module

public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Certificates.CosetTableRelations

public section

namespace CFSG.LieType.Multipliers

open Subgroup CFSG.CosetTable CFSG.Open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}


private theorem pow_val_add {C : Type*} [CommGroup C] {e : ℕ} [NeZero e] {z : C}
    (hz : z ^ e = 1) (a b : ZMod e) : z ^ (a + b).val = z ^ a.val * z ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) e, pow_add, pow_mul, hz, one_pow, mul_one]

private def piHom {C : Type*} [CommGroup C] {r : ℕ} (e : Fin r → ℕ) [∀ j, NeZero (e j)]
    (z : Fin r → C) (hz : ∀ j, z j ^ e j = 1) :
    Multiplicative ((j : Fin r) → ZMod (e j)) →* C where
  toFun a := ∏ j, z j ^ (a.toAdd j).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [toAdd_mul, Pi.add_apply, pow_val_add (hz j)]


end CFSG.LieType.Multipliers
