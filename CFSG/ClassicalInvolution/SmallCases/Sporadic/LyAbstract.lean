module

public import CFSG.Assembly.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.ClassicalInvolution

section Closure

variable {G : Type*} [Group G]


end Closure

section Centralizer

variable {G : Type*} [Group G]


end Centralizer

section Fixed

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem card_centralizer_le_of_fixed [Finite G] (z : G) (ω : Ω) (hz : z • ω = ω) (F : Finset Ω)
    (hF : ∀ x, z • x = x → x ∈ F) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) ≤
      F.card * Nat.card (Subgroup.centralizer ({z} : Set G) ⊓ MulAction.stabilizer G ω :
        Subgroup G) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have horb : Nat.card (MulAction.orbit C ω) * Nat.card (MulAction.stabilizer C ω) =
      Nat.card C := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup C ω)
  have hsub : MulAction.orbit C ω ⊆ (↑F : Set Ω) := by
    rintro _ ⟨⟨c, hc⟩, rfl⟩
    apply hF
    have hzc : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    show z • (c • ω) = c • ω
    rw [← mul_smul, ← hzc, mul_smul, hz]
  have hle : Nat.card (MulAction.orbit C ω) ≤ F.card := by
    rw [Nat.card_coe_set_eq]
    calc (MulAction.orbit C ω).ncard ≤ (↑F : Set Ω).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet F)
      _ = F.card := Set.ncard_coe_finset F
  have hstab : Nat.card (MulAction.stabilizer C ω) =
      Nat.card (C ⊓ MulAction.stabilizer G ω : Subgroup G) := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← horb, hstab]
  exact Nat.mul_le_mul_right _ hle

end Fixed

section Rho

variable {G Ω : Type*} [Group G] [MulAction G Ω]


end Rho

section Alt

open Equiv Equiv.Perm

@[expose] def sig0 : Perm (Fin 11) := swap 1 2 * swap 3 4 * swap 5 6 * swap 9 10

@[expose] def sig1 : Perm (Fin 11) := swap 1 3 * swap 2 4 * swap 6 7 * swap 8 10

@[expose] def sig2 : Perm (Fin 11) := swap 0 1 * swap 3 5 * swap 6 8 * swap 7 9

@[expose] def sigmaOf : Fin 3 → Perm (Fin 11) := ![sig0, sig1, sig2]


end Alt

section Quasisimple

open Equiv Equiv.Perm
open scoped commutatorElement


end Quasisimple

end CFSG.ClassicalInvolution
