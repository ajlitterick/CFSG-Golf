module

public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank


@[expose] def IVK_4_1a_L3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p n : ℕ), p.Prime → p ≠ 2 → IsLnEps 3 K 1 (p ^ n) →
    ∀ z : K, orderOf z = 2 →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (N : Subgroup (GL (Fin 2) F)) (_ : N.Normal),
        Nat.card F = p ^ n ∧ (Nat.card ↥N = 1 ∨ Nat.card ↥N = 3) ∧
          Nonempty (↥(centralizer ({z} : Set K)) ≃* (GL (Fin 2) F ⧸ N))

end CFSG.GH74.GLS.IVK.Proofs2
