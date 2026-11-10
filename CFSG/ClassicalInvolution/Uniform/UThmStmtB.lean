module

public import CFSG.ClassicalInvolution.Uniform.UThmStmtA

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly
open scoped MatrixGroups commutatorElement

@[expose] def Thm6TypedBelowU (p f : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G < n →
      ∀ Ω : Set (Subgroup G), HypOmegaModU (.sl2 p f) Ω → (∀ J ∈ Ω, AEmpty Ω J) → Ω.Nonempty →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) → Disconnected.DEdgeless Ω →
          HasLieTypeU p f Ω .PSL 3 ∨ HasLieTypeU p f Ω .PSU 3 ∨ HasLieTypeU p f Ω .G2 0 ∨
            HasLieTypeU p f Ω .trialityD4 0 ∨ HasM11TypeU p f Ω

@[expose] def Thm7TypedBelowU (p f : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G < n →
      ∀ Ω : Set (Subgroup G), HypOmegaModU (.sl2 p f) Ω → (∀ J ∈ Ω, AEmpty Ω J) →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
          ∀ K ∈ Ω, (∃ K' ∈ twinSet Ω K, K' ≠ K) →
            ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ HasOrthTypeU p f Ω d ε

@[expose] def Thm8TypedBelowU (p f : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G < n →
      ∀ Ω : Set (Subgroup G), HypOmegaModU (.sl2 p f) Ω → (∀ J ∈ Ω, AEmpty Ω J) → Ω.Nonempty →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) → ¬ Disconnected.DEdgeless Ω →
          ¬ Disconnected.DConnected Ω →
            ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ d ≤ 8 ∧ HasOrthTypeU p f Ω d ε

@[expose] def MuTableBelowU (p f : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G < n →
      ∀ Ω : Set (Subgroup G), HypOmegaModU (.sl2 p f) Ω → (∀ J ∈ Ω, AEmpty Ω J) → Ω.Nonempty →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) → ∀ W ∈ WSet Ω,
          (MuIsoZ2 Ω W ↔ ((if piSign p f then HasLieTypeU p f Ω .PSU 3
              else HasLieTypeU p f Ω .PSL 3) ∨ HasM11TypeU p f Ω)) ∧
          (MuIsoS3 Ω W ↔ ((if piSign p f then HasLieTypeU p f Ω .PSL 3
              else HasLieTypeU p f Ω .PSU 3) ∨ HasLieTypeU p f Ω .G2 0 ∨
              HasLieTypeU p f Ω .trialityD4 0)) ∧
          (MuIsoE4 Ω W ↔ (HasOrthTypeU p f Ω 5 true ∨
              HasOrthTypeU p f Ω 6 (!piSign p f) ∨
              (if piSign p f then HasLieTypeU p f Ω .PSU 5 else HasLieTypeU p f Ω .PSL 5))) ∧
          (MuIsoS4 Ω W ↔ (HasOrthTypeU p f Ω 6 (piSign p f) ∨ HasOrthTypeU p f Ω 7 true ∨
              HasOrthTypeU p f Ω 8 false)) ∧
          (HasOrthTypeU p f Ω 8 true → MuIsoWylD4 Ω W) ∧
          (¬ Disconnected.DConnected Ω → MuIsoWylD4 Ω W → HasOrthTypeU p f Ω 8 true)


end CFSG.ClassicalInvolution.Uniform
