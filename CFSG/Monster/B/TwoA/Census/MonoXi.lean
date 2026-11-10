module

public import CFSG.Monster.B.TwoA.Census.MonoData
public import CFSG.Monster.CodeAut.BridgeData

public section

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts Matrix

@[expose] def xiLetter (l : ℕ) : Equiv.Perm (Fin 24) := if l = 0 then bridgePA else bridgePB

@[expose] def xiWordPerm (w : List ℕ) : Equiv.Perm (Fin 24) := (w.map xiLetter).reverse.prod


end CFSG.Monster.B.TwoA.Census
