module

public import CFSG.RankThree.PartOne.CTP.StrongPAssembly

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne (IsStronglyPEmbedded IsSylowOf omegaOne ExtSeitz ExtSPE)
open CFSG.RankThree.PartOne.Census3 (IsoLie TheoremThreeList)
open CFSG.RankThree.PartOne.StrongP
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def Thm3LieIndex (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, q.p ≠ 2 ∧ 5 ≤ q.card ∧ d = .A 1 q) ∨
  (∃ q : TauCeti.PrimePower, q.p ≠ 2 ∧ q.exponent ≤ 3 ∧ (d = .A 2 q ∨ d = .twistedA 2 q)) ∨
  d = .reeG2 1 ∨
  (∃ q : TauCeti.PrimePower, q.p ≠ 2 ∧ q.exponent = 1 ∧
    (d = .G2 q ∨ d = .B 2 q ∨ d = .twistedA 3 q ∨ d = .A 3 q)) ∨
  (∃ q : TauCeti.PrimePower, q.p = 2 ∧ d = .A 1 q) ∨
  (∃ m : ℕ, d = .suzuki m) ∨
  (∃ q : TauCeti.PrimePower, q.p = 2 ∧
    (d = .twistedA 2 q ∨ d = .A 2 q ∨ d = .B 2 q ∨ d = .G2 q ∨ d = .twistedA 3 q ∨
      d = .twistedA 4 q ∨ d = .trialityD4 q)) ∨
  (∃ m : ℕ, d = .reeF4 m) ∨ d = .tits ∨
  (∃ q : TauCeti.PrimePower, q.p = 2 ∧ (d = .A 3 q ∨ d = .B 3 q ∨ d = .twistedD 4 q)) ∨
  (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
    (d = .A 4 q ∨ d = .A 5 q ∨ d = .A 6 q ∨ d = .twistedA 5 q ∨ d = .B 4 q ∨ d = .D 4 q ∨
      d = .F4 q))

@[expose] def ExtSeitzAt (d : TauCeti.LieTypeIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K], (∃ a b : K, a * b ≠ b * a) →
    IsoLie K d → ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ d.characteristic →
      ∀ E : Subgroup (MulAut K), CFSG.IsElementaryAbelian p E → Nat.card E = p ^ 2 →
        Subgroup.closure {k : K | ∃ F : Subgroup (MulAut K), F ≤ E ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} = ⊤ ∨ (p = 5 ∧ (d = .tits ∨ d = .suzuki 2))

@[expose] def ExtSeitzAtInner (d : TauCeti.LieTypeIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K], (∃ a b : K, a * b ≠ b * a) →
    IsoLie K d → ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ d.characteristic →
      ∀ E : Subgroup (MulAut K), CFSG.IsElementaryAbelian p E → Nat.card E = p ^ 2 →
        (∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) →
        Subgroup.closure {k : K | ∃ F : Subgroup (MulAut K), F ≤ E ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} = ⊤ ∨ (p = 5 ∧ (d = .tits ∨ d = .suzuki 2))

@[expose] def ExtSeitzAtOuter (d : TauCeti.LieTypeIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K], (∃ a b : K, a * b ≠ b * a) →
    IsoLie K d → ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ d.characteristic →
      ∀ E : Subgroup (MulAut K), CFSG.IsElementaryAbelian p E → Nat.card E = p ^ 2 →
        ¬ (∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) →
        Subgroup.closure {k : K | ∃ F : Subgroup (MulAut K), F ≤ E ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} = ⊤ ∨ (p = 5 ∧ (d = .tits ∨ d = .suzuki 2))

@[expose] def ExtSeitzThree : Prop :=
  ∀ d : TauCeti.LieTypeIndex, Thm3LieIndex d → ExtSeitzAt d

theorem extSeitzAt_of_inner_outer {d : TauCeti.LieTypeIndex} (hi : ExtSeitzAtInner d)
    (ho : ExtSeitzAtOuter d) : ExtSeitzAt d := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hc
  by_cases h : ∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g
  · exact hi K hnab hiso p hp hp5 hpd E hE hc h
  · exact ho K hnab hiso p hp hp5 hpd E hE hc h


end CFSG.RankThree.PartOne.CTP
