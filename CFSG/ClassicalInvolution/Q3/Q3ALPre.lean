module

public import CFSG.ClassicalInvolution.Q3.Q3ALCent
public import CFSG.ClassicalInvolution.Q3.Q3AEdges
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AL

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD

@[expose] def OddThreeFreePre3 (P : ∀ {G : Type} [Group G], Subgroup G → G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K → P K z →
      ExactMembers3 (conjClass3 K) → Q3W.LocalOddThreeFree3 (conjClass3 K) z

theorem OddThreeFreePre3.mono {P Q : ∀ {G : Type} [Group G], Subgroup G → G → Prop}
    (hQP : ∀ (G : Type) [Group G] (K : Subgroup G) (z : G), Q K z → P K z)
    (h : OddThreeFreePre3 P) : OddThreeFreePre3 Q := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hQ hex
  exact h G hnab K z hz hBelow h3 h4 hΔ (hQP G K z hQ) hex


section Exact


end Exact


end CFSG.ClassicalInvolution.Q3.Q3AL
