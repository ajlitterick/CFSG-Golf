module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Reduction
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Dispatch
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.IndexA
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.IndexU
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.IndexSp
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.IndexOrth
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ExcUntwisted
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ExcE6
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ExcD4
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ExcRee
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ExcSmall
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData

public section

namespace CFSG.StandardType.FF81

open CFSG.StandardType.FF81.CatQ1

theorem catalogueQ1_holds :
    CatalogueQ1 :=
  catalogueQ1_of_clauses CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    (outerThreeBigAt_of_families outerThreeBig_A outerThreeBig_twistedA outerThreeBig_B_two
      outerThreeBig_B_even outerThreeBig_B_odd outerThreeBig_C outerThreeBig_D4
      outerThreeBig_D outerThreeBig_twistedD outerThreeBig_E6 outerThreeBig_E7
      outerThreeBig_E8 outerThreeBig_F4 outerThreeBig_G2 outerThreeBig_twistedE6
      outerThreeBig_trialityD4 outerThreeBig_suzuki outerThreeBig_reeG2 outerThreeBig_reeF4
      outerThreeBig_tits)

end CFSG.StandardType.FF81
