module

public import CFSG.ClassicalInvolution.Asc77.SU4Stmt
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpMain
public import CFSG.ClassicalInvolution.Balance.BootstrapExoticG2D4
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinalTw
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortTwistedE6Frame
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.MilestoneAssemblyWired5
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Main
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Main
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Main
public import CFSG.ClassicalInvolution.RouteD.ExoticD4LinearClique
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleExc
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleOrth
public import CFSG.ClassicalInvolution.RouteD.GapsFrBFinal
public import CFSG.ClassicalInvolution.RouteD.MultiModelFactsFinal
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Row
public import CFSG.ClassicalInvolution.RouteD.SmallBWired
public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainSLs
public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainSUs
public import CFSG.ClassicalInvolution.RouteD.Sp3C4Piece
public import CFSG.ClassicalInvolution.RouteD.TwinSL4BridgeMain
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeNodeLevi
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeFacts
public import CFSG.ClassicalInvolution.RouteD.TypeE8TorGlueWired
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorWired
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptIsolated
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2DatumTwin
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinal
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeFactsCenter
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeFactsUnitary

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.Open (genFittingFStar IsSubnormal classicalInvolutionWitness
  classicalInvolutionTightlyEmbedded lieOrdersChar M11 classicalInvolutionM12)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {p f : ℕ} [Fact p.Prime]

local notation "𝒞" => Generic.CoreAssembly.conjClass

theorem exoticLeviBlockG2D4_proved : ExoticLeviBlockG2D4 p f :=
  fun _ _ _ _ hΩ _ _ h9 D i hi => Balance.exists_member_leviBlockImage_of_g2d4 hΩ h9 D i hi

end CFSG.ClassicalInvolution.MilestoneAssembly
