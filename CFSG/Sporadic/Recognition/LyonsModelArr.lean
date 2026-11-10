module

public import CFSG.Sporadic.Recognition.LyonsModelInputs

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly0

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Equiv

def setOfArr (a : Array UInt32) : Set (Fin deg) := {i | ∃ p ∈ a, p.toNat = i.val}


end CFSG.Sporadic.Recognition.LyonsSims.Ly0
