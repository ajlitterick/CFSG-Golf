module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup CFSG.RankThree.LocalRank

instance thetaOddCore_normal (p : ℕ) (L : Type*) [Group L] :
    (inSubgroup (pPrimeCore 2) (aschbacherSolvableCore p L)).Normal :=
  ConjAct.normal_of_characteristic_of_normal


end CFSG.RankThree.GroupTheory.SteinbergBK
