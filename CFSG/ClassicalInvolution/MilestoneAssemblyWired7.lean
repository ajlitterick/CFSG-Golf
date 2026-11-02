module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnMain
public import CFSG.ClassicalInvolution.MilestoneAssemblyWired6
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeNodeAll

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

end CFSG.ClassicalInvolution.MilestoneAssembly
