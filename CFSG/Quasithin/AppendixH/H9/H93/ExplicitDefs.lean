module

public import CFSG.Quasithin.AppendixH.H9.NaturalDualModel

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

@[expose] def invGL4 (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (h : A * A = 1) : GL (Fin 4) (ZMod 2) :=
  ⟨A, A, h, h⟩


@[expose] def mT02 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def mT03 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def mT12 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def mT13 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]

theorem mT02_sq : mT02 * mT02 = 1 := by decide
theorem mT03_sq : mT03 * mT03 = 1 := by decide
theorem mT12_sq : mT12 * mT12 = 1 := by decide
theorem mT13_sq : mT13 * mT13 = 1 := by decide

@[expose] def gT02 : GL (Fin 4) (ZMod 2) := invGL4 mT02 mT02_sq
@[expose] def gT03 : GL (Fin 4) (ZMod 2) := invGL4 mT03 mT03_sq
@[expose] def gT12 : GL (Fin 4) (ZMod 2) := invGL4 mT12 mT12_sq
@[expose] def gT13 : GL (Fin 4) (ZMod 2) := invGL4 mT13 mT13_sq


@[expose] def vP01_23 (a : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 := ![a 1, a 0, a 3, a 2]
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
