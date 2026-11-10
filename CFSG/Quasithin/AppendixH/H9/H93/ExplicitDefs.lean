module

public import CFSG.Quasithin.AppendixH.H9.NaturalDualModel

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open


@[expose] def vP01 (a : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 := ![a 1, a 0, a 2, a 3]
@[expose] def vP23 (a : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 := ![a 0, a 1, a 3, a 2]
@[expose] def vZJ (a : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  ![a 0 + (a 0 + a 1 + a 2 + a 3), a 1 + (a 0 + a 1 + a 2 + a 3),
    a 2 + (a 0 + a 1 + a 2 + a 3), a 3 + (a 0 + a 1 + a 2 + a 3)]


@[expose] def A2vec (ε a : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  (if ε 0 = 1 then vP01 else id) ((if ε 1 = 1 then vP23 else id)
    ((if ε 2 = 1 then vZJ else id) a))


@[expose] def A2fst (ε a b : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  if ε 3 = 0 then A2vec ε a else A2vec ε b
@[expose] def A2snd (ε a b : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  if ε 3 = 0 then A2vec ε b else A2vec ε a


end CFSG.ASVolI.ChH
