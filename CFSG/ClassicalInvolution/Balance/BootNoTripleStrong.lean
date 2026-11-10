module

public import CFSG.ClassicalInvolution.Balance.BootNoTriple
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalancePow
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.BootRank3

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.StrongBalance
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Statement

@[expose] def StrongPowOn (ord : StatedLieTag → ℕ) (Q : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ t : StatedLieTag, StrongLocalTwoBalanceToralPowOn (ord t) t (Q t)

@[expose] def ToralComponentsAt (p : ℕ) [Fact p.Prime] (ord : StatedLieTag → ℕ)
    (Q : StatedLieTag → ℕ → ℕ → ℕ → Prop) (Ω : Set (Subgroup G)) (A : Subgroup G) (a : G) :
    Prop :=
  ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponentBig L →
    L ≤ memberJoin Ω a → ∀ F₀ : Subgroup G, IsFaithfulFourGroupAt A a L F₀ →
      ∃ (t : StatedLieTag) (n e : ℕ) (hp : p.Prime)
        (ψ : (modelUniv t n p e hp).K →* OddQuot a), Q t n p e ∧ IsFundTag t ∧
          StatedLieAdmissible t n p e ∧ 5 ≤ p ^ e ∧
          ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K ∧ ψ.range = L ∧
          ToralActionPow (ord t) ψ (modOdd a F₀)

theorem StrongPowOn.mono {ord : StatedLieTag → ℕ} {Q Q' : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : StrongPowOn ord Q) (hQ : ∀ t n p e, Q' t n p e → Q t n p e) : StrongPowOn ord Q' :=
  fun t => (h t).mono fun n p e => hQ t n p e


omit [Finite G] in
theorem ToralComponentsAt.mono {ord : StatedLieTag → ℕ}
    {Q Q' : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hQ : ∀ t n p e, Q t n p e → Q' t n p e) {Ω : Set (Subgroup G)} {A : Subgroup G} {a : G}
    (h : ToralComponentsAt p ord Q Ω A a) : ToralComponentsAt p ord Q' Ω A a := by
  intro L hL hbig hjoin F₀ hF
  obtain ⟨t, n, e, hp, ψ, hq, hrest⟩ := h L hL hbig hjoin F₀ hF
  exact ⟨t, n, e, hp, ψ, hQ t n p e hq, hrest⟩

end Statement


section Delta


end Delta

section Boot


@[expose] def GoodBootDataToralExists (p f : ℕ) [Fact p.Prime] (ord : StatedLieTag → ℕ)
    (Q : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      CFSG.ClassicalInvolution.RouteD.DeltaConnected (CoreAssembly.conjClass K) →
      BootData p f (CoreAssembly.conjClass K) → ¬ IndepTriple p f (CoreAssembly.conjClass K) →
      ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
        GoodBootData p f (CoreAssembly.conjClass K) L₀ z₀ A S a ∧
          ∀ b ∈ A, b ≠ 1 → ToralComponentsAt p ord Q (CoreAssembly.conjClass K) A b

theorem GoodBootDataToralExists.mono {ord : StatedLieTag → ℕ}
    {Q Q' : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hQ : ∀ t n p e, Q t n p e → Q' t n p e)
    (h : GoodBootDataToralExists p f ord Q) : GoodBootDataToralExists p f ord Q' := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  obtain ⟨L₀, z₀, A, S, a, hgood, htoral⟩ := h G hnab hp2 hq K z hz hBelow hconn hdata hT
  exact ⟨L₀, z₀, A, S, a, hgood, fun b hb hb1 => (htoral b hb hb1).mono hQ⟩


end Boot

end CFSG.ClassicalInvolution.Balance.BootRank3
