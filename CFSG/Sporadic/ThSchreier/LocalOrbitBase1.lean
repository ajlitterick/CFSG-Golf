
module

public import CFSG.Sporadic.ThSchreier.LocalOrbitBase

public import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.LocalData

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise


theorem localX_mem_H : localX ∈ localH := Subgroup.subset_closure (Set.mem_insert _ _)

theorem localY_mem_H : localY ∈ localH := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

end CFSG.Sporadic.ThSchreier
