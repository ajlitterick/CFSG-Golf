module

public import CFSG.ClassicalInvolution.Asc77.AscC25V1
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Out
public import CFSG.ClassicalInvolution.Asc77.AscT7U1
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

@[expose] def lam {G : Type} [Group G] (R R' : Subgroup G) (t' : G) : Subgroup G :=
  R ⊔ R' ⊔ Subgroup.zpowers t'


section Lam


end Lam

section Main


end Main

end CFSG.ClassicalInvolution.Asc77.C25V
