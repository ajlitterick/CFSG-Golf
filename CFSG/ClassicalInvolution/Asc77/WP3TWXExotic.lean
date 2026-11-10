module

public import CFSG.ClassicalInvolution.RouteD.TWRExoticMain
import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.AscBSE8
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscThmABasic

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
