module

public import CFSG.Certificates.CentralizerPresented
public import CFSG.Certificates.CosetTableRelations

public section

namespace CFSG.CosetTable

open CFSG.Certificates CFSG.Certificates.CosetEnumeration
open scoped commutatorElement

variable {m : ℕ}

@[expose] def wordOfCodes (m : ℕ) (w : List ℕ) : List (Fin m × Bool) :=
  w.flatMap fun c => ((List.finRange m).filter fun i => i.val = c / 2).map fun i => (i, c % 2 == 0)

@[expose] def commWord (a s : List (Fin m × Bool)) : List (Fin m × Bool) :=
  FreeGroup.invRev a ++ FreeGroup.invRev s ++ a ++ s


end CFSG.CosetTable
