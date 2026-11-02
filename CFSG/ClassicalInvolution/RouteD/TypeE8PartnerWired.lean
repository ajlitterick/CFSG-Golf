module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternWired
public import CFSG.ClassicalInvolution.RouteD.TypeE8PartnerAt

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

theorem e8PartnerExists_of_inputs_at (hMFZ : Gaps.FundNoncentral p) (hG : E7SignPerp p f)
    (hT : E8TorusFixed p f) (hX : TypeE8.E8ClassExcluded p f) : E8PartnerExists p f := by
  intro G _ _ _ hnab K z S hS
  exact exists_partnerAt_E8_at hMFZ S.odd S.five S.inClass S.exact (mem_conjClass_self K)
    (single_class K) S.cls hS S.p1 (TypeEPattern.layerGeom_E7_of_signPerp S.five hG)
    (hT G hnab K z S hS) (hX G hnab K z S hS)

end CFSG.ClassicalInvolution.MilestoneAssembly
