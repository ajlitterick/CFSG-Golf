module

public import CFSG.ClassicalInvolution.Q3.Q3PWeak

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Vocabulary

variable {G : Type} [Group G]

abbrev conjClass3 (K : Subgroup G) : Set (Subgroup G) :=
  Set.range fun g : G => conjSub g K

@[expose] def IndepTriple3 (Ω : Set (Subgroup G)) : Prop :=
  ∃ (K : Fin 3 → Subgroup G) (z : Fin 3 → G),
    (∀ i, K i ∈ Ω ∧ IsClassicalMember3 (K i) (z i)) ∧ (∀ i j, i ≠ j → Commutes (K i) (K j)) ∧
    IsElemAbelian 2 (Subgroup.closure (Set.range z)) ∧
    Nat.card (Subgroup.closure (Set.range z)) = 8

@[expose] def BootData3 (Ω : Set (Subgroup G)) : Prop :=
  ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G), L₀ ∈ Ω ∧ IsClassicalMember3 L₀ z₀ ∧
    IsElemAbelian 2 A ∧ Nat.card A = 8 ∧ z₀ ∈ A ∧ L₀ ≤ Subgroup.centralizer (A : Set G)


@[expose] def Setup3 (K : Subgroup G) (z : G) : Prop :=
  ExactMembers3 (conjClass3 K) ∧ LocalOddCentral (conjClass3 K) {z}

end Vocabulary

section Branches


@[expose] def BootTriple3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      IndepTriple3 (conjClass3 K) → Setup3 K z


end Branches

end CFSG.ClassicalInvolution.Q3
