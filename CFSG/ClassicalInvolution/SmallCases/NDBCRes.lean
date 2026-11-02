module

public import CFSG.ClassicalInvolution.SmallCases.NDBStmt

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]

@[expose] def HasTwin (K : Subgroup G) (z : G) : Prop :=
  ∃ T ∈ 𝒞 K, T ≠ K ∧ IsClassicalMember p f T z

@[expose] def HasTwoTwins (K : Subgroup G) (z : G) : Prop :=
  ∃ T₁ ∈ 𝒞 K, ∃ T₂ ∈ 𝒞 K, T₁ ≠ K ∧ T₂ ≠ K ∧ T₁ ≠ T₂ ∧ IsClassicalMember p f T₁ z ∧
    IsClassicalMember p f T₂ z

@[expose] def TwinShapeWeak (K : Subgroup G) (z : G) : Prop :=
  Asc77.TwinLieShape p f (𝒞 K) z ∧ HasTwin p f K z

@[expose] def NoDataShapeCoverWeak : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      Disconnected.DConnected (𝒞 K) → ¬ BootData p f (𝒞 K) →
        (∃ A : Subgroup G, Balance.Theorem5.FuzzyFrameOn p f (𝒞 K) A) ∨
          Asc77.ChainShape p f (𝒞 K) z ∨ TwinShapeWeak p f K z ∨ PSpShape p f (𝒞 K) z

@[expose] def NoAllA1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z →
      ∀ D : Balance.LocalLieSystemAt p f (Asc77.ExactLayer.exactFamily (𝒞 K) z) z,
        ¬ ∀ i, D.tag i = .PSL ∧ D.rank i = 2

@[expose] def NoExoticSingle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → ¬ HasTwin p f K z →
      ∀ D : Balance.LocalLieSystemAt p f (Asc77.ExactLayer.exactFamily (𝒞 K) z) z, ∀ i,
        ¬ (D.tag i = .G2 ∨ D.tag i = .trialityD4 ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
          (D.tag i = .POmegaMinus ∧ D.rank i = 4))

@[expose] def NoG2D4Twin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → HasTwin p f K z →
      ∀ D : Balance.LocalLieSystemAt p f (Asc77.ExactLayer.exactFamily (𝒞 K) z) z, ∀ i,
        ¬ (D.tag i = .G2 ∨ D.tag i = .trialityD4)

@[expose] def NoD4Twins : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → HasTwoTwins p f K z →
      ∀ D : Balance.LocalLieSystemAt p f (Asc77.ExactLayer.exactFamily (𝒞 K) z) z, ∀ i,
        ¬ (D.tag i = .POmegaPlus ∧ D.rank i = 4)

end CFSG.ClassicalInvolution.NDB
