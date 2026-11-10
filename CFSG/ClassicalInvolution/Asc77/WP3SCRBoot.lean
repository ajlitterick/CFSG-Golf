module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootMain
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootNoTwins
public import CFSG.ClassicalInvolution.Asc77.AscFusionB

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem hypOmegaModAll_of_fusionCore (h : AscFusion.FusionCoreStmt p f) :
    HypOmegaModAll p f :=
  AscHypOmega.hypOmegaAllStmt_of_fusion (AscFusion.classicalFusionStmt_of_fusionCore h)


end CFSG.ClassicalInvolution.Asc77
