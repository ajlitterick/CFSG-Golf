module

public import CFSG.ClassicalInvolution.Q3.Q3TEdge
public import CFSG.ClassicalInvolution.Q3.M11OddCore
public import CFSG.ClassicalInvolution.Balance.Theorem5Untouched
public import CFSG.ClassicalInvolution.Q3.ExactDelta
public import CFSG.ClassicalInvolution.Q3.StrongBalance

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

theorem modelOddCentralizerFree3_proved : ModelOddCentralizerFree3 :=
  modelOddCentralizerFree3_of_tags fun t ht => by
    by_cases hex : ExceptionalFundTag3 t
    · rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact oddCentralizerFreeTag_G2
      · exact oddCentralizerFreeTag_F4
      · exact oddCentralizerFreeTag_E6
      · exact oddCentralizerFreeTag_E7
      · exact oddCentralizerFreeTag_E8
      · exact oddCentralizerFreeTag_twistedE6
      · exact oddCentralizerFreeTag_trialityD4
    · exact oddCentralizerFreeTag_of_classical ht hex

theorem lieSystemOddCentralizer3_proved : LieSystemOddCentralizer3 :=
  lieSystemOddCentralizer3_of_modelFacts CFSG.ClassicalInvolution.ModelFacts.modelClauseZero
    modelOddCentralizerFree3_proved

theorem IsEdge3.card_pair {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K₁ K₂ : Subgroup G} {z₁ z₂ : G} (h : IsEdge3 Ω K₁ K₂ z₁ z₂) :
    Nat.card (Subgroup.closure ({z₁, z₂} : Set G)) = 4 :=
  card_closure_pair_eq_four h.cls₁.isCentralInvolution.sq h.cls₂.isCentralInvolution.sq
    h.cls₁.ne_one h.cls₂.ne_one h.ne h.comm_involutions

theorem IsEdge3.isElemAbelian_pair {G : Type} [Group G] {Ω : Set (Subgroup G)}
    {K₁ K₂ : Subgroup G} {z₁ z₂ : G} (h : IsEdge3 Ω K₁ K₂ z₁ z₂) :
    IsElemAbelian 2 (Subgroup.closure ({z₁, z₂} : Set G)) := by
  refine Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_
  · intro s hs
    rcases hs with rfl | hs
    · exact h.cls₁.isCentralInvolution.sq
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact h.cls₂.isCentralInvolution.sq
  · intro s hs t ht
    rcases hs with rfl | hs <;> rcases ht with rfl | ht
    · rfl
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      exact h.comm_involutions
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact h.comm_involutions.symm
    · rw [Set.mem_singleton_iff] at hs ht
      subst hs ht
      rfl

section Alpha

variable {G : Type} [Group G]


end Alpha

section Setup

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

@[expose] def TypeC3Alpha : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ →
        alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥


variable {K : Subgroup G} {z : G}


end Setup

section Axis

variable {G : Type} [Group G]

structure EdgeAxis3 (z₁ z₂ : G) (A : Subgroup G) : Prop where
  pair_le : Subgroup.closure ({z₁, z₂} : Set G) ≤ A
  balance : RankThreeBalance A
  generation : rankTwoSpan A = ⊤

namespace EdgeAxis3

variable {z₁ z₂ : G} {A : Subgroup G}

theorem pair_mem [Finite G] {Ω : Set (Subgroup G)} {K₁ K₂ : Subgroup G}
    (h : EdgeAxis3 z₁ z₂ A) (he : IsEdge3 Ω K₁ K₂ z₁ z₂) :
    Subgroup.closure ({z₁, z₂} : Set G) ∈ signalizerFunctorEk 2 2 A :=
  ⟨h.pair_le, by rw [he.card_pair]; norm_num⟩

theorem alphaCore_eq_bot [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : EdgeAxis3 z₁ z₂ A) {F : Subgroup G} (hF : F ∈ signalizerFunctorEk 2 2 A) :
    alphaCore F = ⊥ := by
  have hnorm : (Theorem5.alphaFrame A).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (Theorem5.alphaFrame A : Set G) :=
      Theorem5.rankTwoSpan_le_normalizer_alphaFrame h.balance
        (h.generation ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hle := CFSG.ComponentClassification.OddCore.maximal G (Theorem5.alphaFrame A) hnorm
    (Theorem5.odd_card_alphaFrame h.balance)
  rw [componentClassificationOddCore_eq_bot_of_simple hnab] at hle
  rw [← Theorem5.alphaFrame_eq_alphaCore h.balance hF]
  exact le_bot_iff.mp hle

end EdgeAxis3

end Axis


end CFSG.ClassicalInvolution.Q3
