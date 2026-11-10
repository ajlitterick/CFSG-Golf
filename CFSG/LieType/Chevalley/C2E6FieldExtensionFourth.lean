module

public import CFSG.LieType.Chevalley.C2E6FieldExtensionResidue
public import CFSG.LieType.Chevalley.C2E6FourthResidueOpposite

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FieldExtension

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open FourthResidue (V0 Qminus sMinus rhoMinus fourthJ two_mem_fourthJ)

theorem sO_mul_self : FourthResidue.sO * FourthResidue.sO = 1 :=
  Subtype.ext FourthResidue.sMinus_mul_self

abbrev sHom :
    betaGroup →* TauCeti.QuadraticMap.orthogonalGroup Qminus :=
  betaGroupHom FourthResidue.sO sO_mul_self


end CFSG.LieType.Chevalley.C2E6Std.FieldExtension
