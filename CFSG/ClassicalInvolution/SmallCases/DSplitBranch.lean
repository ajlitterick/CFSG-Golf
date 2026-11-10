module

public import CFSG.ClassicalInvolution.SmallCases.DSplitBridge
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedInputs

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly

variable (p f : ℕ) [Fact p.Prime]

structure DBranchD {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  below : CITBelowU p f (Nat.card G)
  member : IsClassicalMember p f K z
  rank : 3 ≤ CFSG.Open.twoRank G
  notFourGenerated : ¬ TwoSubgroupsFourGenerated G
  dDisconnected : ¬ DConnected (CoreAssembly.conjClass K)

variable {p f}

theorem DBranchD.toDBranch {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (h : DBranchD p f K z) : DBranch p f K z where
  nonabelian := h.nonabelian
  odd := h.odd
  five := h.five
  below := h.below
  member := h.member
  rank := h.rank
  notFourGenerated := h.notFourGenerated
  disconnected := fun hΔ => h.dDisconnected (dConnected_of_deltaConnected hΔ)

variable (p f)

structure TightBranchD {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  branch : DBranchD p f K z
  control : ControlC K
  edgeless : DEdgeless (CoreAssembly.conjClass K)

theorem TightBranchD.toTightBranch {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (h : TightBranchD p f K z) : TightBranch p f K z :=
  ⟨h.branch.toDBranch, h.control, deltaEdgeless_of_dEdgeless h.edgeless⟩


@[expose] def SmallDisconnectedD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11


end CFSG.ClassicalInvolution.Disconnected
