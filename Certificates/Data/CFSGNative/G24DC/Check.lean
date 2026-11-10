module

public import Std.Data.HashMap

public section

namespace CFSG.Quasithin.St84.G24DC.Native

abbrev Row := Nat × Nat

abbrev Mat := Array Row

@[expose] def zeroRow : Row := (0, 0)

@[expose] def rowVal (r : Row) (j : Nat) : Nat :=
  (r.1.testBit j).toNat + 2 * (r.2.testBit j).toNat

@[expose] def mask14 : Nat := (1 <<< 14) - 1

@[expose] def canon (r : Row) : Row := (r.1 &&& mask14, r.2 &&& mask14)

@[expose] def xorRow (p q : Row) : Row := canon (p.1 ^^^ q.1, p.2 ^^^ q.2)

@[expose] def oneM : Mat := ((List.finRange 14).map fun i => (1 <<< i.val, 0)).toArray

@[expose] def omegaCode (b : Nat) : Nat :=
  (b >>> 1) ||| (((b &&& 1) ^^^ (b >>> 1)) <<< 1)

@[expose] def scalarMul (a b : Nat) : Nat :=
  if a = 0 then 0
  else if a = 1 then b
  else if a = 2 then omegaCode b
  else omegaCode b ^^^ b

@[expose] def scale (a u v : Nat) : Row :=
  if a = 0 then zeroRow
  else if a = 1 then canon (u, v)
  else if a = 2 then canon (v, u ^^^ v)
  else canon (u ^^^ v, u)

@[expose] def mulRow (a : Row) (B : Mat) : Row :=
  (List.range 14).foldl (fun (p : Row) j =>
    xorRow p (scale (rowVal a j) (B.getD j zeroRow).1 (B.getD j zeroRow).2)) zeroRow

@[expose] def mulN (A B : Mat) : Mat :=
  ((List.finRange 14).map fun i => mulRow (A.getD i.val zeroRow) B).toArray


@[expose] def evalP (im : Array Mat) (w : List Nat) : Mat :=
  w.foldl (fun acc l => mulN acc (im.getD l oneM)) oneM

@[expose] def evalF (im : Array Mat) (w : List (Fin 4)) : Mat :=
  w.foldl (fun acc l => mulN acc (im.getD l.val oneM)) oneM


@[expose] def gBN (_ : Unit := ()) : Array Mat :=
  #[#[⟨1, 1⟩, ⟨0, 2⟩, ⟨0, 4⟩, ⟨0, 8⟩, ⟨16, 0⟩, ⟨0, 32⟩, ⟨64, 0⟩, ⟨128, 0⟩, ⟨256, 256⟩, ⟨512, 0⟩, ⟨1024, 1024⟩, ⟨2048, 2048⟩, ⟨4096, 4096⟩, ⟨0, 8192⟩],
 #[⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 4⟩, ⟨8, 8⟩, ⟨16, 16⟩, ⟨32, 0⟩, ⟨64, 0⟩, ⟨128, 0⟩, ⟨256, 0⟩, ⟨0, 512⟩, ⟨0, 1024⟩, ⟨2048, 2048⟩, ⟨4096, 0⟩, ⟨8192, 0⟩],
 #[⟨1, 0⟩, ⟨46, 0⟩, ⟨36, 0⟩, ⟨40, 0⟩, ⟨592, 0⟩, ⟨32, 0⟩, ⟨64, 0⟩, ⟨640, 0⟩, ⟨7424, 0⟩, ⟨512, 0⟩, ⟨5120, 0⟩, ⟨6144, 0⟩, ⟨4096, 0⟩, ⟨8192, 0⟩],
 #[⟨3, 0⟩, ⟨2, 0⟩, ⟨4, 0⟩, ⟨24, 0⟩, ⟨16, 0⟩, ⟨416, 0⟩, ⟨320, 0⟩, ⟨128, 0⟩, ⟨256, 0⟩, ⟨1536, 0⟩, ⟨1024, 0⟩, ⟨2048, 0⟩, ⟨12288, 0⟩, ⟨8192, 0⟩]]


@[expose] def wWords : List (List (List (Fin 4))) :=
  [[[0], [1], [2], [3]],
   [[0, 0], [1, 1], [2], [3]],
   [[0, 0], [1], [2], [2, 3, 2, 3, 2, 3, 2]],
   [[0], [1, 1], [2], [2, 3, 2, 3, 2, 3, 2]],
   [[0], [1], [2], [3]],
   [[0], [1], [2], [0, 2, 3, 2, 3, 2, 3, 0, 2, 3, 0]],
   [[0], [1], [2], [0, 3, 0, 2, 3, 2, 3, 2, 3, 0, 2]],
   [[0], [1], [2], [2, 3, 2, 3, 2, 3, 2]],
   [[0, 0], [1, 1], [2], [3]],
   [[0, 0], [1, 1], [2], [0, 3, 0, 2, 3, 2, 3, 2, 3, 0, 2]],
   [[0, 0], [1, 1], [2], [0, 2, 3, 2, 3, 2, 3, 0, 2, 3, 0]],
   [[0, 0], [1, 1], [2], [2, 3, 2, 3, 2, 3, 2]]]

@[expose] def wImgN (_ : Unit := ()) : Array (Array Mat) :=
  let g := gBN ()
  (wWords.map fun row => (row.map (evalF g)).toArray).toArray


end CFSG.Quasithin.St84.G24DC.Native
