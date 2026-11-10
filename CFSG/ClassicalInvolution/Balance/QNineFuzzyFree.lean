module

public import CFSG.ClassicalInvolution.Balance.Q27FuzzyMain
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyBoot

public section

namespace CFSG.ClassicalInvolution.Balance.Q27

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Balance.Theorem5
  (conjMembers TriangleConnectedAll TriangleLayers conjInvariant_conjMembers
    fuzzyAxisExact_conjMembers fuzzyMemberConn_conjMembers fuzzyVertexConn_of_adj)

variable {p f : ℕ} [Fact p.Prime]


theorem bootTriple_conjMembers_free_exotic (hlay : TriangleLayers p f)
    (hmodel : LayerGenerationHybrid p) (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hexotic : ExoticLeviBlock p f) : CoreAssembly.BootTriple p f :=
  Theorem5.bootTriple_of_fuzzyFrames_exotic conjMembers hlay
    (fun _ _ _ K => conjInvariant_conjMembers K) (fuzzyFrameBalance_of_hybrid_free hmodel)
    fuzzyAxisExact_conjMembers
    (fuzzyVertexConn_of_adj fuzzyMemberConn_conjMembers fuzzyEdgeInFrame_conjMembers_free)
    (fuzzyLinkConn_conjMembers_free hMFC) hexotic

theorem triangleConnectedAll_conjMembers_free_exotic (hlay : TriangleLayers p f)
    (hmodel : LayerGenerationHybrid p) (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hexotic : ExoticLeviBlock p f) : TriangleConnectedAll p f :=
  triangleConnectedAll_of_bootTriple (bootTriple_conjMembers_free_exotic hlay hmodel hMFC hexotic)
    (fuzzyFramesConnected_conjMembers_free hMFC)


end CFSG.ClassicalInvolution.Balance.Q27
