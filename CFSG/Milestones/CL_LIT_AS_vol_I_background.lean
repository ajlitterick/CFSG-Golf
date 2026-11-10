module

public import Mathlib
public import CFSG.Open.Catalog
public import CFSG.Open.Defs
public import CFSG.Open.QuasithinDefs
public import CFSG.Open.QuasithinH1NaturalModulesMilestoneDefs
public import CFSG.Milestones.ASVolI.Bundle
public import CFSG.Quasithin.Background.ASVolIRegistered

public section

universe u v w

namespace CFSG.Open

open CFSG.Open in
open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.cl_lit_as_vol_i_background_1
    (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) (H : Subgroup PSL(2, GaloisField p f)) :
    (IsElemAbelian p H ∧ ∃ m : ℕ, m ≤ f ∧ Nat.card H = p ^ m) ∨
    (IsCyclic H ∧ (Nat.card H ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨
      Nat.card H ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1))) ∨
    (∃ z : ℕ, (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨
      z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
    (16 ∣ p ^ (2 * f) - 1 ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
    ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
    (∃ (m t : ℕ) (P : Subgroup H) (_ : P.Normal), IsElemAbelian p P ∧
      Nat.card P = p ^ m ∧ IsCyclic (H ⧸ P) ∧ Nat.card (H ⧸ P) = t ∧ t ∣ p ^ m - 1 ∧
      t ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∨
    (∃ m : ℕ, m ∣ f ∧ Nonempty (H ≃* PSL(2, GaloisField p m))) ∨
    (∃ m : ℕ, 2 * m ∣ f ∧ Nonempty (H ≃* PGL(2, GaloisField p m))) := by
  exact CFSG.Open.ASVolIRegistered.red_1 p f hf H


end CFSG.Open

namespace CFSG.Open


end CFSG.Open

namespace CFSG.Open


end CFSG.Open

namespace CFSG.Open


end CFSG.Open

namespace CFSG.Open

section

end

section

end

end CFSG.Open
