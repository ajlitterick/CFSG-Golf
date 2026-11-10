module

public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagDefs
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.BootRank3

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.StrongBalance
open CFSG.ClassicalInvolution.Balance.LocalBalance (subgroupOf_involutionOddCore_le)
open CFSG.Open (IsElemAbelian)
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (conjSp)
open scoped commutatorElement MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Transfer

variable {X : Type*} [Group X] {N : Subgroup X}

theorem ToralDiagGL.subgroupOf {k n : ℕ} {F : Type} [Field F] {ψ : SL(n, F) →* X}
    {ψ' : SL(n, F) →* N} (hψ : ∀ y, (ψ' y : X) = ψ y) {F₀ : Subgroup X}
    (h : ToralDiagGL k ψ F₀) : ToralDiagGL k ψ' (F₀.subgroupOf N) := by
  obtain ⟨P, hP, hact⟩ := h
  refine ⟨P, hP, fun f hf => ?_⟩
  obtain ⟨x, hxP, hxk, hxa⟩ := hact f.1 hf
  refine ⟨x, hxP, hxk, fun y => Subtype.ext ?_⟩
  have h := hxa y
  rw [← hψ y, ← hψ (slConjugation n F x y)] at h
  exact h

theorem ToralDiagGU.subgroupOf {k : ℕ} {K : Type} [Field K] [Finite K] {p' f₀ : ℕ}
    [Fact p'.Prime] [CharP K p'] {n : ℕ} {ψ : Su K p' f₀ n →* X} {ψ' : Su K p' f₀ n →* N}
    (hψ : ∀ y, (ψ' y : X) = ψ y) {F₀ : Subgroup X} (h : ToralDiagGU k ψ F₀) :
    ToralDiagGU k ψ' (F₀.subgroupOf N) := by
  obtain ⟨P, hP, hact⟩ := h
  refine ⟨P, hP, fun f hf => ?_⟩
  obtain ⟨x, hxP, hxk, hxa⟩ := hact f.1 hf
  refine ⟨x, hxP, hxk, fun y => Subtype.ext ?_⟩
  have h := hxa y
  rw [← hψ y,
    ← hψ (conjSUid (CFSG.LieType.BorelTits.unitaryInvolution K p' f₀) n x y)] at h
  exact h

theorem ToralDiagGSp.subgroupOf {k n : ℕ} {F : Type} [Field F] {ψ : StatedSp n F →* X}
    {ψ' : StatedSp n F →* N} (hψ : ∀ y, (ψ' y : X) = ψ y) {F₀ : Subgroup X}
    (h : ToralDiagGSp k ψ F₀) : ToralDiagGSp k ψ' (F₀.subgroupOf N) := by
  obtain ⟨P, hP, hact⟩ := h
  refine ⟨P, hP, fun f hf => ?_⟩
  obtain ⟨x, hxP, hxk, hxa⟩ := hact f.1 hf
  refine ⟨x, hxP, hxk, fun y => Subtype.ext ?_⟩
  have h := hxa y
  rw [← hψ y, ← hψ (conjSp n F x y)] at h
  exact h

theorem ToralDiagOrth.subgroupOf {k : ℕ} {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {ψ : spinGroup Q →* X} {ψ' : spinGroup Q →* N}
    (hψ : ∀ y, (ψ' y : X) = ψ y) {F₀ : Subgroup X} (h : ToralDiagOrth k ψ F₀) :
    ToralDiagOrth k ψ' (F₀.subgroupOf N) := by
  obtain ⟨P, hP, hO, hact⟩ := h
  refine ⟨P, hP, hO, fun f hf => ?_⟩
  obtain ⟨s, hsP, hsk, α, hα, hαa⟩ := hact f.1 hf
  refine ⟨s, hsP, hsk, α, hα, fun y => Subtype.ext ?_⟩
  have h := hαa y
  rw [← hψ y, ← hψ (α y)] at h
  exact h

theorem ToralActionDiag.subgroupOf {k : ℕ} {t : StatedLieTag} {n p' e : ℕ} {hp : p'.Prime}
    {X' : Type} [Group X'] {N' : Subgroup X'} {ψ : (modelUniv t n p' e hp).K →* X'}
    {ψ' : (modelUniv t n p' e hp).K →* N'} (hψ : ∀ y, (ψ' y : X') = ψ y) {F₀ : Subgroup X'}
    (h : ToralActionDiag k t n p' e hp ψ F₀) :
    ToralActionDiag k t n p' e hp ψ' (F₀.subgroupOf N') := by
  have : Fact p'.Prime := ⟨hp⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_,
    fun h1 h2 h3 h4 h5 h6 => ?_⟩
  · obtain ⟨ε, hε⟩ := h1 ht
    exact ⟨ε, ToralDiagGL.subgroupOf (fun y => hψ _) hε⟩
  · obtain ⟨ε, hε⟩ := h2 ht
    exact ⟨ε, ToralDiagGU.subgroupOf (fun y => hψ _) hε⟩
  · obtain ⟨ε, hε⟩ := h3 ht
    exact ⟨ε, ToralDiagGSp.subgroupOf (fun y => hψ _) hε⟩
  · obtain ⟨ε, hε⟩ := h4 ht
    exact ⟨ε, ToralDiagOrth.subgroupOf (fun y => hψ _) hε⟩
  · obtain ⟨ε, hε⟩ := h5 ht
    exact ⟨ε, ToralDiagOrth.subgroupOf (fun y => hψ _) hε⟩
  · obtain ⟨ε, hε⟩ := h6 ht
    exact ⟨ε, ToralDiagOrth.subgroupOf (fun y => hψ _) hε⟩
  · obtain ⟨P, hP, hact⟩ := h7 h1 h2 h3 h4 h5 h6
    refine ⟨P, hP, fun f hf => ?_⟩
    obtain ⟨x, hxP, hxk, hxa⟩ := hact f.1 hf
    refine ⟨x, hxP, hxk, fun y => Subtype.ext ?_⟩
    have h := hxa y
    rw [← hψ y, ← hψ (x * y * x⁻¹)] at h
    exact h

end Transfer

section Statement

@[expose] def DeltaDiagOn (k : ℕ) (t : StatedLieTag) (Q : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), Q n p e → IsFundTag t → StatedLieAdmissible t n p e →
    p ≠ 2 → 5 ≤ p ^ e →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K → ψ.range.Normal →
      ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
        (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) →
        ToralActionDiag k t n p e hp ψ F → ∀ d ∈ deltaCore F, ∀ x ∈ ψ.range, d * x = x * d

@[expose] def DeltaDiagAll (ord : StatedLieTag → ℕ)
    (Q : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ t : StatedLieTag, DeltaDiagOn (ord t) t (Q t)

theorem DeltaDiagOn.mono {k : ℕ} {t : StatedLieTag} {Q Q' : ℕ → ℕ → ℕ → Prop}
    (h : DeltaDiagOn k t Q) (hQ : ∀ n p e, Q' n p e → Q n p e) : DeltaDiagOn k t Q' :=
  fun n p e hp hq => h n p e hp (hQ n p e hq)

theorem DeltaDiagAll.mono {ord : StatedLieTag → ℕ} {Q Q' : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : DeltaDiagAll ord Q) (hQ : ∀ t n p e, Q' t n p e → Q t n p e) : DeltaDiagAll ord Q' :=
  fun t => (h t).mono fun n p e => hQ t n p e

@[expose] def ToralComponentsDiagAt (p : ℕ) [Fact p.Prime] (ord : StatedLieTag → ℕ)
    (Q : StatedLieTag → ℕ → ℕ → ℕ → Prop) (Ω : Set (Subgroup G)) (A : Subgroup G) (a : G) :
    Prop :=
  ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponentBig L →
    L ≤ memberJoin Ω a → ∀ F₀ : Subgroup G, IsFaithfulFourGroupAt A a L F₀ →
      ∃ (t : StatedLieTag) (n e : ℕ) (hp : p.Prime)
        (ψ : (modelUniv t n p e hp).K →* OddQuot a), Q t n p e ∧ IsFundTag t ∧
          StatedLieAdmissible t n p e ∧ 5 ≤ p ^ e ∧
          ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K ∧ ψ.range = L ∧
          ToralActionDiag (ord t) t n p e hp ψ (modOdd a F₀)

end Statement


section Delta


end Delta

section Boot


@[expose] def GoodBootDataDiagExists (p f : ℕ) [Fact p.Prime] (ord : StatedLieTag → ℕ)
    (Q : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      CFSG.ClassicalInvolution.RouteD.DeltaConnected (CoreAssembly.conjClass K) →
      BootData p f (CoreAssembly.conjClass K) → ¬ IndepTriple p f (CoreAssembly.conjClass K) →
      ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
        GoodBootData p f (CoreAssembly.conjClass K) L₀ z₀ A S a ∧
          ∀ b ∈ A, b ≠ 1 → ToralComponentsDiagAt p ord Q (CoreAssembly.conjClass K) A b

theorem GoodBootDataDiagExists.mono {ord : StatedLieTag → ℕ}
    {Q Q' : StatedLieTag → ℕ → ℕ → ℕ → Prop} (hQ : ∀ t n p e, Q t n p e → Q' t n p e)
    (h : GoodBootDataDiagExists p f ord Q) : GoodBootDataDiagExists p f ord Q' := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  obtain ⟨L₀, z₀, A, S, a, hgood, htoral⟩ := h G hnab hp2 hq K z hz hBelow hconn hdata hT
  refine ⟨L₀, z₀, A, S, a, hgood, fun b hb hb1 => ?_⟩
  intro L hL hbig hjoin F₀ hF
  obtain ⟨t, n, e, hp, ψ, hq', rest⟩ := htoral b hb hb1 L hL hbig hjoin F₀ hF
  exact ⟨t, n, e, hp, ψ, hQ t n p e hq', rest⟩


end Boot

end CFSG.ClassicalInvolution.Balance.BootRank3
