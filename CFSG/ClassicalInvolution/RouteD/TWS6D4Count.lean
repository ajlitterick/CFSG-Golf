module

public import CFSG.ClassicalInvolution.RouteD.TWS6D4MF
public import CFSG.ClassicalInvolution.RouteD.TWYCount
public import CFSG.ClassicalInvolution.RouteD.TWYEven
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS6

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.RouteD.TWY
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.GroupTheory.WeirSylow (IsPlusType isPlusType_quadPlus)
open CFSG.ClassicalInvolution.ModelFacts (plusSp minusSp mem_plusSp mem_minusSp
  isCompl_plusSp_minusSp polar_plusSp_minusSp)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

end CFSG.ClassicalInvolution.RouteD.TWS6
