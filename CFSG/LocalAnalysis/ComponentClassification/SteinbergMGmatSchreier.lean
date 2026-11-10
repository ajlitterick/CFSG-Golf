module

public import CFSG.LocalAnalysis.ComponentClassification.SteinbergMGmatInner

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence CFSG.Monster.Visible

instance hmat_Qmat_normal : (Qmat.subgroupOf Hmat).Normal :=
  gmat_rhoQvis_normal


end CFSG.ComponentClassification.BMCase
