module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternWired
public import CFSG.ClassicalInvolution.RouteD.TypeE8TorGlue
public import CFSG.ClassicalInvolution.RouteD.GapsChainConfig
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorGeom

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

theorem e8TorusFixed_of_model (hB1 : TypeE8.E7PairFrame p f) (hB5 : TypeE8.E7TorusFixedModel p f) :
    E8TorusFixed p f := by
  intro G _ _ _ _ K z _ hshape c j hj hjimg β hβ t htβ hKβ hβ0 ht
  exact c.torusFixedE7_of_node_system hB1 hB5 (single_class K) hshape hj hjimg hβ htβ hKβ hβ0 ht

theorem e8TorusFixed_of_frame_toral (hB1 : TypeE8.E7PairFrame p f) (hF : TypeE8.E7A1A4Frame p f)
    (hT : TypeE8.E7A1A4Toral p f) : E8TorusFixed p f :=
  e8TorusFixed_of_model hB1 (TypeE8.e7TorusFixedModel_of_frame_toral p f hF hT)

end CFSG.ClassicalInvolution.MilestoneAssembly
