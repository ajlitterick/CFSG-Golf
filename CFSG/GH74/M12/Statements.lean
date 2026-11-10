module

public import CFSG.GH74.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial

public section

namespace CFSG.GH74.M12

open Subgroup CFSG.Blueprint

abbrev M12Group : Type := NativeSporadic.Carrier .M12


@[expose] def q8Subgroups {H : Type*} [Group H] (Q : Subgroup H) : Set (Subgroup H) :=
  {K | K ≤ Q ∧ Nonempty (↥K ≃* QuaternionGroup 2)}

structure Asc03Hyp (G : Type*) [Group G] (z : G) : Prop where
  orderTwo : orderOf z = 2
  card_core : Nat.card ↥(CFSG.pCore 2 ↥(centralizer ({z} : Set G))) = 32
  extraspecial : IsExtraspecial 2 ↥(CFSG.pCore 2 ↥(centralizer ({z} : Set G)))
  quotient_S3 : Nonempty (↥(centralizer ({z} : Set G)) ⧸ CFSG.pCore 2 ↥(centralizer ({z} : Set G))
    ≃* Equiv.Perm (Fin 3))
  centralizer_X : ∀ X : Sylow 3 ↥(centralizer ({z} : Set G)),
    ∀ q ∈ CFSG.pCore 2 ↥(centralizer ({z} : Set G)), (∀ x ∈ X, x * q = q * x) →
      (q : G) ∈ zpowers z
  not_weakly_closed : ∃ g : G, g * z * g⁻¹ ≠ z ∧
    ∃ q ∈ CFSG.pCore 2 ↥(centralizer ({z} : Set G)), (q : G) = g * z * g⁻¹

@[expose] def S_Asc03_Theorem1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Asc03Hyp G z →
    (∃ (V : Subgroup G) (_ : V.Normal), IsElementaryAbelian 2 ↥V ∧ Nat.card ↥V = 8 ∧
        Nonempty (G ⧸ V ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∨
    ((Nonempty (G ≃* alternatingGroup (Fin 8)) ∨ Nonempty (G ≃* alternatingGroup (Fin 9))) ∧
        ∀ K ∈ q8Subgroups (CFSG.pCore 2 ↥(centralizer ({z} : Set G))), ¬ K.Normal) ∨
    (NativeSporadic.IsSporadic G .M12 ∧
        ∀ K ∈ q8Subgroups (CFSG.pCore 2 ↥(centralizer ({z} : Set G))), K.Normal)

@[expose] def S_Asc03_simple : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ z : G, Asc03Hyp G z →
    (∃ K ∈ q8Subgroups (CFSG.pCore 2 ↥(centralizer ({z} : Set G))), K.Normal) →
      NativeSporadic.IsSporadic G .M12

@[expose] def S_M12_core : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → Nat.card G = 95040 →
    ∀ z : G, Asc03Hyp G z →
      (∃ K ∈ q8Subgroups (CFSG.pCore 2 ↥(centralizer ({z} : Set G))), K.Normal) →
        NativeSporadic.IsSporadic G .M12


@[expose] def bfE : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 1, 3, 2] * List.formPerm [4, 5, 11, 9, 8, 10, 7, 6]

@[expose] def bfN : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [5, 6] * List.formPerm [7, 11] * List.formPerm [9, 10]

@[expose] def bfF : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 2] * List.formPerm [4, 5, 7, 9, 8, 10, 11, 6]

@[expose] def bfX : Equiv.Perm (Fin 12) := bfE⁻¹ * bfF * bfE * bfF⁻¹

@[expose] def bfJ : Equiv.Perm (Fin 12) := bfF ^ 4

@[expose] def bfS : Subgroup (Equiv.Perm (Fin 12)) := Subgroup.closure {bfE, bfN, bfF}

theorem bfF_pow_mem (n : ℕ) : bfF ^ n ∈ bfS :=
  Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) n


end CFSG.GH74.M12
