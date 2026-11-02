module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternExcl
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternWired
public import CFSG.ClassicalInvolution.RouteD.GapsChainConfig
public import CFSG.ClassicalInvolution.RouteD.GapsOrthPairs

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

theorem e7PartnerExists_of_torusFixed (hMFZ : Gaps.FundNoncentral p) (hT : E7TorusFixed p f) :
    E7PartnerExists p f := by
  intro G _ _ _ hnab K z S hS
  exact exists_partnerAt_E7_of_torus hMFZ S.odd S.five S.inClass S.exact (mem_conjClass_self K)
    (single_class K) S.cls hS S.p1 (hT G hnab K z S hS)

end CFSG.ClassicalInvolution.MilestoneAssembly
