module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyRows
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedStatements
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedA2

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly

section Control

variable {G : Type} [Group G]


end Control

section Branch

variable (p f : ℕ) [Fact p.Prime]

structure DBranch {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  below : CITBelowU p f (Nat.card G)
  member : IsClassicalMember p f K z
  rank : 3 ≤ CFSG.Open.twoRank G
  notFourGenerated : ¬ TwoSubgroupsFourGenerated G
  disconnected : ¬ DeltaConnected K

omit [Fact p.Prime] in
theorem smallDisconnected_iff [Fact p.Prime] :
    SmallDisconnected p f ↔ ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
      (K : Subgroup G) (z : G), DBranch p f K z →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 := by
  constructor
  · intro h G _ _ _ K z hb
    exact h G hb.nonabelian hb.odd hb.five hb.below K z hb.member hb.rank hb.notFourGenerated
      hb.disconnected
  · intro h G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hΔ
    exact h G K z ⟨hnab, hp2, hq, hBelow, hz, h3, h4, hΔ⟩

@[expose] def SmallDisconnectedControlled : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranch p f K z → ControlC K →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def SmallDisconnectedUncontrolled : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranch p f K z → ¬ ControlC K →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

variable {p f}

theorem smallDisconnected_of_split (hc : SmallDisconnectedControlled p f)
    (hu : SmallDisconnectedUncontrolled p f) : SmallDisconnected p f := by
  rw [smallDisconnected_iff]
  intro G _ _ _ K z hb
  by_cases hC : ControlC K
  · exact hc G K z hb hC
  · exact hu G K z hb hC


end Branch

end CFSG.ClassicalInvolution.Disconnected
