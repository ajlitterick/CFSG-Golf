module

public import CFSG.ClassicalInvolution.RouteD.TWS6D4Count
public import CFSG.ClassicalInvolution.RouteD.TWYRankEven
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS6

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.RouteD.TWY
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap

local notation "𝒞" => CoreAssembly.conjClass


end CFSG.ClassicalInvolution.RouteD.TWS6
