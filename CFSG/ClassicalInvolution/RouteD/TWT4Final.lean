module

public import CFSG.ClassicalInvolution.RouteD.TWT4Assemble
public import CFSG.ClassicalInvolution.RouteD.TWT4Cent
public import CFSG.ClassicalInvolution.RouteD.TWT4Hbad

public section

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.TWZ CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

