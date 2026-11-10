module

public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetup
public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetupFrame
public import CFSG.ClassicalInvolution.Balance.BootNoTriple
public import CFSG.ClassicalInvolution.Balance.Theorem5Core
public import CFSG.ClassicalInvolution.Balance.BootstrapLevi
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyCanon
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Generic.TypeCSetup

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Alpha

variable [Finite G]

theorem alphaCore_eq_bot_of_rankTwoSpan_eq_top {A : Subgroup G}
    (hO : componentClassificationOddCore G = ⊥) (hA : RankThreeBalance A)
    (htop : rankTwoSpan A = ⊤) {F : Subgroup G} (hF : F ∈ signalizerFunctorEk 2 2 A) :
    alphaCore F = ⊥ := by
  have hnorm : (Theorem5.alphaFrame A).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (Theorem5.alphaFrame A : Set G) :=
      Theorem5.rankTwoSpan_le_normalizer_alphaFrame hA (htop ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hle := CFSG.ComponentClassification.OddCore.maximal G (Theorem5.alphaFrame A) hnorm
    (Theorem5.odd_card_alphaFrame hA)
  rw [hO] at hle
  rw [← Theorem5.alphaFrame_eq_alphaCore hA hF]
  exact le_bot_iff.mp hle

end Alpha


structure BalancedEdge (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K₁ K₂ : Subgroup G) (z₁ z₂ : G) (A : Subgroup G) : Prop where
  mem₁ : K₁ ∈ Ω
  mem₂ : K₂ ∈ Ω
  cls₁ : IsClassicalMember p f K₁ z₁
  cls₂ : IsClassicalMember p f K₂ z₂
  comm : Commutes K₁ K₂
  ne : z₁ ≠ z₂
  pair_le : Subgroup.closure ({z₁, z₂} : Set G) ≤ A
  balance : RankThreeBalance A
  generation : rankTwoSpan A = ⊤

namespace BalancedEdge

variable [Finite G] {Ω : Set (Subgroup G)} {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {A : Subgroup G}

theorem card_pair (h : BalancedEdge p f Ω K₁ K₂ z₁ z₂ A) :
    Nat.card (Subgroup.closure ({z₁, z₂} : Set G)) = 4 :=
  card_closure_pair_eq_four h.cls₁.isCentralInvolution.sq h.cls₂.isCentralInvolution.sq
    h.cls₁.ne_one h.cls₂.ne_one h.ne (h.comm z₁ h.cls₁.mem z₂ h.cls₂.mem)

theorem pair_mem (h : BalancedEdge p f Ω K₁ K₂ z₁ z₂ A) :
    Subgroup.closure ({z₁, z₂} : Set G) ∈ signalizerFunctorEk 2 2 A :=
  ⟨h.pair_le, by rw [h.card_pair]; norm_num⟩


omit [Finite G] in
theorem le_centralizer₁ (h : BalancedEdge p f Ω K₁ K₂ z₁ z₂ A) :
    K₁ ≤ Subgroup.centralizer (Subgroup.closure ({z₁, z₂} : Set G) : Set G) := by
  rw [Subgroup.centralizer_closure]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact (Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.RouteD.le_centralizer_of_isClassicalMember h.cls₁ hk)).symm
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (h.comm k hk _ h.cls₂.mem).symm


end BalancedEdge


section Refined


end Refined

end CFSG.ClassicalInvolution.Generic.TypeCSetup
