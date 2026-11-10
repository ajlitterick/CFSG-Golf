module

public import CFSG.ClassicalInvolution.Balance.BootNoTripleDStage
public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetupInputs
public import CFSG.ClassicalInvolution.SmallCases.DSplitBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.BootRank3

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure FuzzyBalancedDataD (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Ω : Set (Subgroup G)) (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G))
    (a : G) : Prop where
  mem : L₀ ∈ Ω
  cls : IsClassicalMember p f L₀ z₀
  z₀A : z₀ ∈ A
  tq : A ≤ trivialOnQuot L₀
  balance : RankThreeBalance A
  frame : FrameSideTwoD p f Ω A S
  aA : a ∈ A
  a1 : a ≠ 1
  aClassical : ∃ M ∈ Ω, IsClassicalMember p f M a
  cover : ∀ K ∈ centMembers Ω a, ¬ IsClassicalMember p f K a →
    ∃ g : G, a ∈ conjSub g A ∧ InCommonComponent a K (conjSub g L₀)
  nine : p ^ f = 9 → ∃ x ∈ A, x ≠ 1 ∧ (∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
    InCommonComponent x K (conjSub g L₀)) ∧ LocalLeviComponent p f Ω x

namespace FuzzyBalancedDataD

variable {L₀ : Subgroup G} {z₀ : G} {A : Subgroup G} {S : Set (Subgroup G)} {a : G}

theorem cent [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hconn : DConnected Ω)
    (h : FuzzyBalancedDataD p f Ω L₀ z₀ A S a) : L₀ ≤ Subgroup.centralizer (A : Set G) := by
  have hO := componentClassificationOddCore_eq_bot_of_simple hnab
  have hgen : rankTwoSpan A = ⊤ := rankTwoSpan_eq_top_of_dConnected hp2 hq hΩ h.frame hconn
  have hc := h.cls.isCentralInvolution
  have hz2 : z₀ * z₀ = 1 := h.balance.mul_self h.z₀A
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  by_cases hg1 : g = 1
  · rw [hg1, one_mul, mul_one]
  by_cases hgz : g = z₀
  · rw [hgz]
    exact hc.central x hx
  have hg2 : g * g = 1 := h.balance.mul_self hg
  have hcomm : z₀ * g = g * z₀ := h.balance.comm h.z₀A hg
  have hFA : Subgroup.closure ({z₀, g} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact h.z₀A
    · rw [Set.mem_singleton_iff.mp hy]
      exact hg
  have hcard : Nat.card (Subgroup.closure ({z₀, g} : Set G)) = 4 :=
    card_closure_pair_eq_four hz2 hg2 hc.ne_one hg1 (fun e => hgz e.symm) hcomm
  have hF : Subgroup.closure ({z₀, g} : Set G) ∈ signalizerFunctorEk 2 2 A :=
    ⟨hFA, by rw [hcard]; norm_num⟩
  have hα : alphaCore (Subgroup.closure ({z₀, g} : Set G)) = ⊥ :=
    TypeCSetup.alphaCore_eq_bot_of_rankTwoSpan_eq_top hO h.balance hgen hF
  exact Theorem5.mem_centralizer_of_alphaCore_eq_bot h.cls (h.tq hg) hg2 hc.ne_one hα x hx

end FuzzyBalancedDataD


end CFSG.ClassicalInvolution.Disconnected
