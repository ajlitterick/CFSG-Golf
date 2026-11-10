module

public import CFSG.Sporadic.HNSchreier.Schreier
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch
public import CFSG.Sporadic.M23.M23Group

public section

namespace CFSG.Sporadic.HNSchreier

open CFSG.ComponentClassification.SporadicSchreierDispatch

theorem sporadicSchreierCase_HN :
    SporadicSchreierCase .HN :=
  sporadicSchreierCase_of_outer AT_HN_Schreier

end CFSG.Sporadic.HNSchreier
