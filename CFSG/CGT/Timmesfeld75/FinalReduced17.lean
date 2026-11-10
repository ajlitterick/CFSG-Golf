module

public import CFSG.CGT.Timmesfeld75.FinalReduced14
public import CFSG.CGT.Timmesfeld75.Sec63Close
public import CFSG.CGT.Timmesfeld75.Sec3TenExc
public import CFSG.CGT.Timmesfeld75.Sec57Close
public import CFSG.CGT.Timmesfeld75.Sec63Final
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.CGT.Timmesfeld75

theorem sec4NoA_of_inputs
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (h26 : Lemma26Input) (hI : Sec4CaseIInputs2) (hE : Sec4CaseIIIEight) : Sec4NoA := by
  have h214 := lemma214_of_remaining L
  have hIII : Sec4CaseIII := sec4CaseIII_of_inputs h214 involutionClassInput_of_repo hSz
    L.aschbacherTheoremOne benderWCInput_of_repo hE
  have hCI : Sec4CaseI := sec4CaseI_of_inputs h214 involutionClassInput_of_repo
    L.aschbacherTheoremOne benderWCInput_of_repo aschbacherNoPolarInput_of_repo
    (sec4I4TrivialAction_of_inputs aschbacherNoPolarInput_of_repo
      (lemma215_of_literature
        (LiteratureInputs.of_reduced (ReducedLiteratureInputs.of_remaining L)))
      h26 hI.rootGroup)
    hI.outerAction hI.outerAction5 hI.goldschmidt
  exact sec4NoA_of_cases hCI hIII

end CFSG.CGT.Timmesfeld75
