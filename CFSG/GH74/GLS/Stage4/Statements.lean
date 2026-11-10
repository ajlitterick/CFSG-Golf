module

public import CFSG.GH74.GLS.Stage4.Ree
public import CFSG.GH74.GLS.SP.GlueDefs

public section

namespace CFSG.GH74.GLS.Stage4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.GH74.BNPair CFSG.GH74.GLS.SP

@[expose] def IsTwoCentralG2TypeG2 (G : Type) [Group G] (Gs : Type) [Group Gs] : Prop :=
  (∃ (S : Sylow 2 G) (S' : Sylow 2 Gs), Nonempty (↥(S : Subgroup G) ≃* ↥(S' : Subgroup Gs))) ∧
    ∃ z : G, IsCentralInvolution z ∧ (∀ u : G, orderOf u = 2 → IsConj z u) ∧
      pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ ∧
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel Gs .G2 0 p f ∧
        HasSL2ProductOfIndexTwoCh6 (oPrimeResidual 2 ↥(centralizer ({z} : Set G))) (p ^ f)

theorem IsTwoCentralG2Type.g2 {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs]
    (hnonab : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G))
    (h : IsTwoCentralG2Type G Gs) : IsTwoCentralG2TypeG2 G Gs := by
  obtain ⟨-, hS, z, hz, hconj, hO, hbr⟩ := h
  refine ⟨hS, z, hz, hconj, hO, ?_⟩
  rcases hbr with ⟨-, K, hK, p, f, hp, h8, -, hL⟩ | h
  · exact (not_ree_branch hnonab hz hK h8 hL).elim
  · exact h

@[expose] def RootOrdersG2 {G : Type} [Group G] (root : ℤ → Subgroup G) (q : ℕ) : Prop :=
  ∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card ↥(root i) = q

@[expose] def RootOrdersD4 {G : Type} [Group G] (root : ℤ → Subgroup G) (q : ℕ) : Prop :=
  (∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card ↥(root i) = if i % 2 = 1 then q ^ 3 else q) ∨
    (∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card ↥(root i) = if i % 2 = 1 then q else q ^ 3)


end CFSG.GH74.GLS.Stage4
