module

public import CFSG.ClassicalInvolution.RouteD.TWRExoticTriple
public import CFSG.ClassicalInvolution.RouteD.TWRExoticOrders
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootMain
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Row
public import CFSG.ClassicalInvolution.Balance.BootNoTriple
public import CFSG.ClassicalInvolution.SmallCases.DSplitDefs
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8

public section

namespace CFSG.ClassicalInvolution.RouteD.TWR

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

end CFSG.ClassicalInvolution.RouteD.TWR
