module

public import CFSG.GH74.KGroups.U33Inputs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier CFSG.Certificates


@[expose] def commB (a b : Equiv.Perm (Fin 28)) : Bool :=
  (List.finRange 28).all fun i => a (b i) == b (a i)


@[expose] def centList (LP : List (Equiv.Perm (Fin 28))) (g : Equiv.Perm (Fin 28)) :
    List (Equiv.Perm (Fin 28)) :=
  LP.filter (commB g)


end CFSG.OddStandard.SmallF3.HarrisU33.S4B
