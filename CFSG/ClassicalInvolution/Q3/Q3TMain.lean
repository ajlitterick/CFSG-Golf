module

public import CFSG.ClassicalInvolution.Q3.Q3TAxis

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

@[expose] def TypeC3Rec : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K → Setup3 K z →
      Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K →
      Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11


end CFSG.ClassicalInvolution.Q3
