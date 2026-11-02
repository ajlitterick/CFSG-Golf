module

public import CFSG.ClassicalInvolution.SmallCases.NDBCRes

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]

@[expose] def D4FiveCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    (∃ x y : G, x * y ≠ y * x) → p ≠ 2 → 5 ≤ p ^ f → IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → Disconnected.DConnected (𝒞 K) →
        (∀ A : Subgroup G, ¬ Balance.Theorem5.FuzzyFrameOn p f (𝒞 K) A) →
          ∀ D : Balance.LocalLieSystemAt p f (Asc77.ExactLayer.exactFamily (𝒞 K) z) z, ∀ i,
            (D.tag i = .POmegaPlus ∧ D.rank i = 4) → D.card = 5 → False

end CFSG.ClassicalInvolution.NDB
