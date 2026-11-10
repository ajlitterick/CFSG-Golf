module

public import CFSG.GH74.KGH
public import CFSG.GH74.Constrained
public import CFSG.GH74.SmallRanks
public import CFSG.GH74.Statements

public section

namespace CFSG.GH74

open Subgroup Blueprint Assembly.LowTwoRank

@[expose] def S_walterNative : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G) →
      (∃ f : ℕ, 2 ≤ f ∧ LieModel G .PSL 2 2 f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ LieModel G .PSL 2 p f) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ LieModel G .twistedG2 0 3 f) ∨
      NativeSporadic.IsSporadic G .J1

@[expose] def S_noComponent : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → KGH G →
    (∀ x : G, orderOf x = 2 → layerBar x = ⊥) → GH74Conclusion G


theorem sylow_not_comm_of_not_comm {G : Type*} [Group G] [Finite G]
    (h : ¬ ∃ S : Sylow 2 G, IsMulCommutative (S : Subgroup G)) (S : Sylow 2 G) :
    ¬ IsMulCommutative (S : Subgroup G) :=
  fun hS => h ⟨S, hS⟩

section Cases

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem gh74Conclusion_of_abelian (hW : S_walterNative) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank : 3 ≤ Open.twoRank G) (hgen : Gen4 G) (S : Sylow 2 G)
    (hS : IsMulCommutative (S : Subgroup G)) : GH74Conclusion G := by
  rcases hW G hnonab S hS with ⟨f, hf, h⟩ | ⟨p, f, hp, hp2, hf, -, -, h⟩ | ⟨f, -, -, h⟩ | h
  · have hrankf : Open.twoRank G = f := twoRank_eq_of_lieModel_PSL_two_two h
    have h4 : Open.twoRank G ≤ 4 := hgen.twoRank_le
    have hf3 : f = 3 ∨ f = 4 := by omega
    rcases hf3 with rfl | rfl
    · exact GH74Conclusion.of_eight (Or.inl h)
    · exact GH74Conclusion.of_eight (Or.inr (Or.inl h))
  · have := twoRank_le_two_of_lieModel_PSL_two_odd hp hp2 h
    omega
  · exact Or.inr (Or.inr (Or.inl ⟨f, h⟩))
  · exact GH74Conclusion.of_J1 h


end Cases


end CFSG.GH74
