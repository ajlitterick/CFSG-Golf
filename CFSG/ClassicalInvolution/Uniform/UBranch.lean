module

public import CFSG.ClassicalInvolution.Uniform.UIH8
public import CFSG.ClassicalInvolution.Uniform.USat

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups

section Branch

variable (p f : ℕ)

structure DBranchU {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  odd : p ≠ 2
  three : 3 ≤ p ^ f
  below : CITBelowT (.sl2 p f) (Nat.card G)
  member : IsClassicalMemberU (.sl2 p f) K z
  rank : 3 ≤ CFSG.Open.twoRank G
  notFourGenerated : ¬ TwoSubgroupsFourGenerated G
  dDisconnected : ¬ DConnected (CoreAssembly.conjClass (satU (.sl2 p f) K z))

variable {p f}

namespace DBranchU

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem member_satU (h : DBranchU p f K z) :
    IsClassicalMemberU (.sl2 p f) (satU (.sl2 p f) K z) z :=
  h.member.satU_member

theorem intrinsic_satU (_h : DBranchU p f K z) :
    IsIntrinsicU (.sl2 p f) (satU (.sl2 p f) K z) z :=
  isIntrinsicU_satU _ K z

end DBranchU

@[expose] def HypOmegaModDU (p f : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z → HypOmegaModU (.sl2 p f) (CoreAssembly.conjClass (satU (.sl2 p f) K z))

@[expose] def AEmptyDU (p f : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z → ∀ J ∈ CoreAssembly.conjClass (satU (.sl2 p f) K z),
      AEmpty (CoreAssembly.conjClass (satU (.sl2 p f) K z)) J


end Branch

section Facades


end Facades

end CFSG.ClassicalInvolution.Uniform
