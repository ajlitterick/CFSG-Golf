module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameLieE
public import CFSG.ClassicalInvolution.Asc77.WP3FrameStarE
import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

section Inputs

variable (p f : ℕ) [Fact p.Prime]

@[expose] def HypOmegaModAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → HypOmegaMod p f (CoreAssembly.conjClass K)


@[expose] def ChainFrameGenT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K J K' : Subgroup G) (z t z' : G), ChainFrameSetting p f Ω K J K' z t z' →
      CentralizerGenerationStar Ω (Subgroup.closure ({z, t, z'} : Set G)) t


end Inputs

section Frames


end Frames

end CFSG.ClassicalInvolution.Asc77
