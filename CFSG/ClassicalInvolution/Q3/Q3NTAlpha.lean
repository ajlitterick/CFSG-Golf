module

public import CFSG.ClassicalInvolution.Q3.Q3NTLemmaD

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap

section Statement


@[expose] def AlphaCent3Under (P : ∀ {G : Type} [Group G], Subgroup G → G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K → P K z →
      ∀ (K₁ L : Subgroup G) (z₁ w : G), K₁ ∈ conjClass3 K → L ∈ conjClass3 K →
        IsClassicalMember3 K₁ z₁ → IsClassicalMember3 L w → z₁ ≠ w →
        L ≤ Subgroup.centralizer ({z₁} : Set G) →
        alphaCore (Subgroup.closure ({z₁, w} : Set G)) = ⊥

theorem AlphaCent3Under.mono {P Q : ∀ {G : Type} [Group G], Subgroup G → G → Prop}
    (hQP : ∀ (G : Type) [Group G] (K : Subgroup G) (z : G), Q K z → P K z)
    (h : AlphaCent3Under P) : AlphaCent3Under Q := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hQ
  exact h G hnab K z hz hBelow h3 h4 hΔ (hQP G K z hQ)


end Statement

section Pair


end Pair

section Setup


end Setup

end CFSG.ClassicalInvolution.Q3
