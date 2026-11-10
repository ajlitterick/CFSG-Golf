module

public import Certificates.Data.SmithD6Model

public noncomputable section

namespace CFSG.SmithD6

@[expose] def ea7Bits : List Nat := [2, 3, 4, 5, 8, 9, 14, 15, 16, 17, 22, 23, 26, 27, 28, 29]

@[expose] def ea7Diff (k m : Nat) : Nat := (tvCols k)[m]! ^^^ 2 ^ m

@[expose] def ea7Pivot (k : Nat) : Bool :=
  (List.range 32).all fun m₀ => ea7Diff k m₀ == 0 ||
    (List.range 32).any fun j => (ea7Diff k m₀).testBit j &&
      (List.range 32).all fun m => m == m₀ || !(ea7Diff k m).testBit j

@[expose] def ea7ChkCols : Bool := ea7Pivot 0 && ea7Pivot 31899

@[expose] def ea7ChkBits : Bool :=
  (List.range 32).all fun m => ea7Bits.contains m == (ea7Diff 0 m == 0 && ea7Diff 31899 m == 0)

@[expose] def ea7ChkW : Bool :=
  ea7Bits.all fun m => (List.range 75735).any fun i => wt i == 2 ^ m

@[expose] def ea7InX (p : Nat) : Bool := decide (p < 365211) && tvImg p 0 == 0 && tvImg p 31899 == 31899

@[expose] def ea7I : List Nat := (List.range 365211).filter ea7InX

@[expose] def ea7Restr (p : Nat) : List Nat :=
  let A := tvCols p
  ea7Bits.map fun m => applyCols A (2 ^ m)

@[expose] def ea7ChkF4 : Bool :=
  let R := ea7I.map fun p => (p, ea7Restr p)
  R.all fun a => R.all fun b => a.1 == b.1 || a.2 != b.2

@[expose] def ea7InF0 (p : Nat) : Bool := p == 0 || p == 31899 || ea7InX p

@[expose] def ea7Triple (k : Nat) : List Nat :=
  [(linePair k).1, (linePair k).2, (linePair k).1 ^^^ (linePair k).2]

@[expose] def ea7RigData : List (Nat × Nat × Nat) :=
  [(1, 0, 31), (2, 0, 557), (4, 1579, 1583), (8, 1579, 3675), (16, 1583, 3675), (32, 1591, 3683),
    (64, 557, 31899), (128, 31, 31899), (256, 3747, 7899), (512, 1655, 7963), (1024, 1719, 3811),
    (2048, 1847, 3939)]

@[expose] def ea7ChkRig : Bool :=
  (List.range 12).all (fun i => ea7RigData.any fun t => t.1 == 2 ^ i) &&
  ea7RigData.all fun t => ea7InF0 t.2.1 && ea7InF0 t.2.2 && (ea7Triple t.2.1).contains t.1 &&
    (ea7Triple t.2.2).contains t.1 &&
    (ea7Triple t.2.1).all fun y => !(ea7Triple t.2.2).contains y || y == t.1


@[expose] def ea7InY (bs : List Nat) (q : Nat) : Bool := ea7InX q && bs.all fun b => tvImg q b == b


@[expose] def ea7Bases : List Nat := [142115, 8163, 303839, 31, 1083]

@[expose] def ea7Sizes : List Nat := [1575, 864, 128, 3, 2]


@[expose] def ea7IsA (a : Nat) : Bool := a == 31 || a == 557 || a == 1083


end CFSG.SmithD6
