module

public import CFSG.ClassicalInvolution.SmallCases.DSplitBranch

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

structure TightStd {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  branch : DBranchD p f K z
  normEq : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G)
  edgeless : DEdgeless (CoreAssembly.conjClass K)

structure TightStdDelta {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  branch : DBranch p f K z
  normEq : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G)
  edgeless : DeltaEdgeless K

variable {p f} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem TightStd.toTightBranch (h : TightStd p f K z) : TightStdDelta p f K z :=
  ⟨h.branch.toDBranch, h.normEq, deltaEdgeless_of_dEdgeless h.edgeless⟩


end CFSG.ClassicalInvolution.Disconnected.AschTight.S19R
