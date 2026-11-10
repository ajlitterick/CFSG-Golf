module

public import Certificates.Data.AE6ModelCore

public section

namespace Certificates.AE6Model

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Th.Native Certificates.S7Twin

@[expose] def sLetters : List ℕ := [0, 2, 4, 6]

@[expose] def sGens (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let G := curtisPerms ()
  sLetters.map fun i => G.getD i 1

@[expose] def sDerive : List (List ℤ) := [[-2, 3, 2], [-5, 4, 5], [-4, -2, 4, 2]]

@[expose] def sQ (_ : Unit := ()) : RawSchreierDatum 360 :=
  certificate (by decide) (sGens ()) sDerive #v[0, 2, 4, 24, 8] (by decide)

@[expose] def czLetters : List ℕ := [0, 1, 2, 4, 5, 6, 7]

@[expose] def czGens (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let G := curtisPerms ()
  czLetters.map fun i => G.getD i 1

@[expose] def czDerive : List (List ℤ) :=
  [[-3, 4, 3], [-8, 6, 8], [-6, -3, 6, 3], [-6, -9, -4, -8, -1, -8, -1, -2, 10, 1, 8, 1]]

@[expose] def czQ (_ : Unit := ()) : RawSchreierDatum 360 :=
  certificate (by decide) (czGens ()) czDerive #v[0, 2, 4, 24, 8] (by decide)


@[expose] def spanQ (R Y : Table) : List Table :=
  let R2 := compT 360 R R
  [idT 360, R2, R, compT 360 R R2, Y, compT 360 Y R2, compT 360 R Y, compT 360 Y R]

@[expose] def twinPairs (_ : Unit := ()) : List (Equiv.Perm (Fin 360) × Equiv.Perm (Fin 360)) :=
  let K := k0Gens ()
  let x := K.getD 0 1
  let y := K.getD 1 1
  (cPerms ()).map fun c => (c * x * c⁻¹, c * y * c⁻¹)


@[expose] def cutWord : List ℕ := [1, 5, 7]

@[expose] def cutPerm (_ : Unit := ()) : Equiv.Perm (Fin 360) := aeWord (curtisPerms ()) cutWord

@[expose] def conjWords : List (List ℕ) := [[], [0], [1], [2], [4], [5], [6], [7]]

@[expose] def conjPerms (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let G := curtisPerms ()
  conjWords.map (aeWord G)


end Certificates.AE6Model
