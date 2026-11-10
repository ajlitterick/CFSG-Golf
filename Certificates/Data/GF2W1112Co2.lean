module

public import Certificates.Data.CFSGNative.GF2W1112.Irr
public import Certificates.Data.CFSGNative.Co2.Data

public section

namespace CFSG.GF2W1112

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2.Native CFSG.Sporadic.Th.Native
  CFSG.Perm.Native


@[expose] def w12Co2QRows : Array Nat := #[1, 2, 4, 7, 8, 63, 82, 127, 255, 104, 1177, 2709, 5111, 438, 28308, 24128, 2357, 111011, 290128, 172992, 24380, 326320]

@[expose] def w12AddRows22 (X Y : Array Nat) : Array Nat :=
  Array.ofFn (n := 22) fun i => (X[i.val]?.getD 0) ^^^ (Y[i.val]?.getD 0)

@[expose] def w12Co2F0Rows (_ : Unit := ()) : Array Nat :=
  w12AddRows22 w12Co2QRows (transposeRows 22 w12Co2QRows)

@[expose] def w12Co2Rep (i : Nat) : Nat := if i == 0 then 40 else if i == 1 then 65536 else 8


@[expose] def w12WordRows (rowsA rowsB : Array Nat) (w : List Bool) : Array Nat :=
  w.foldl (fun acc b => mulRows 22 acc (if b then rowsA else rowsB)) (idRows 22)

@[expose] def w12Co2RowsA (_ : Unit := ()) : Array Nat := (co2Data ()).rowsA

@[expose] def w12Co2RowsB (_ : Unit := ()) : Array Nat := (co2Data ()).rowsB

@[expose] def w12Co2QT (_ : Unit := ()) : Array Nat := transposeRows 22 w12Co2QRows

@[expose] def w12Co2FT (_ : Unit := ()) : Array Nat := transposeRows 22 (w12Co2F0Rows ())


end CFSG.GF2W1112
