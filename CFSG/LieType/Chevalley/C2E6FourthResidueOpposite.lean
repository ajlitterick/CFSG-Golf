module

public import CFSG.LieType.Chevalley.C2E6FourthResidueWeyl

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FourthResidue

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Chevalley.CosetBuilding

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def wJ :
    relWeylTwist TwistTag.E6 :=
  (nativeSimple 0 * nativeSimple 1 * nativeSimple 2) ^ 3


end CFSG.LieType.Chevalley.C2E6Std.FourthResidue
