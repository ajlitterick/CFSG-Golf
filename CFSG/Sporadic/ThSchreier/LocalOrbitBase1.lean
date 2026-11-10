
module

public import CFSG.Sporadic.ThSchreier.LocalOrbitBase

public import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise


theorem localX_mem_H : localX ∈ localH := Subgroup.subset_closure (Set.mem_insert _ _)

theorem localY_mem_H : localY ∈ localH := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

end CFSG.Sporadic.ThSchreier
