module

public import CFSG.Holt.H78.Sec4Holt
import CFSG.Holt.H78.Sec4Prop46D5

public import CFSG.GH74.Uniqueness.Bender.UnitaryAut
public import CFSG.Holt.H78.Sec4SEAutFix
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.StronglyEmbedded.BenderNormalSeries

public section

namespace CFSG.Holt.H78

theorem holtCaseAStepA7Statement : HoltCaseAStepA7Statement :=
  fun _ _ _ _ _ _ _ _ hS _ _ _ hP => hS.caseAStepA7 hP

theorem holtTheorem1 : HoltTheorem1 :=
  holtTheorem1_of_caseAStepA7 holtCaseAStepA7Statement

end CFSG.Holt.H78
