module

public import Certificates.Data.CFSGNative.MonsterAxis.Dense

public section

namespace CFSG.Monster.AxisCount.Native

open CFSG.Monster.B.Rep4371.Native (bmaskN wordN)

namespace Cover

@[specialize, expose] def allFrom (p : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | lo, len + 1 => if p lo then allFrom p (lo + 1) len else false

@[specialize, expose] def countGo (p : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => countGo p n (if p n then acc + 1 else acc)

@[inline, expose] def countBelow (p : Nat → Bool) (n : Nat) : Nat := countGo p n 0

@[specialize, expose] def parAll (n chunks : Nat) (p : Nat → Bool) : Bool :=
  let sz := n / chunks + 1
  ((List.range chunks).map fun j =>
    Task.spawn fun _ => allFrom p (j * sz) (min sz (n - j * sz))).all Task.get

@[inline, expose] def rd8 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat


@[inline, expose] def rd32 (b : ByteArray) (i : Nat) : Nat :=
  let o := 4 * i
  (b.get! o).toNat ||| ((b.get! (o + 1)).toNat <<< 8) ||| ((b.get! (o + 2)).toNat <<< 16) |||
    ((b.get! (o + 3)).toNat <<< 24)


@[expose] def actGo (rows : Array Nat) (v : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc => actGo rows v i (if v.testBit i then acc ^^^ rows[i]! else acc)

@[expose] def actRows (rows : Array Nat) (v : Nat) : Nat := actGo rows v 24 0


@[expose] def deltaCount (_ : Unit := ()) : Nat := 8292375


@[expose] def jListC : List Nat := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16]

@[expose] def ellC (j i : Nat) : Int :=
  if j < 12 then (if (bmaskN j).testBit i then 2 else 0)
  else if i = jListC.getD (j - 12) 0 then -3 else 1

@[expose] def ginvListC : List Nat :=
  [57344, 126976, 585728, 4255744, 8450048, 13176832, 40960, 49152, 389120, 258048, 2682880,
   1634304, 28478, 4169567, 4169631, 3567583, 3171106, 582144, 581888, 420900, 124928, 123904, 40,
   48]

@[expose] def sumToC (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumToC f n + f n

@[expose] def pairBit (w : Nat → Int) (k : Nat) : Bool :=
  (sumToC (fun i => w i * ellC k i) 24 / 8) % 2 == 1

@[expose] def solveGo (w : Nat → Int) : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc => solveGo w k (if pairBit w k then acc ^^^ ginvListC.getD k 0 else acc)

@[expose] def clsCoord (w : Nat → Int) : Nat := solveGo w 24 0

@[expose] def rowsOfAct (act : (Nat → Int) → Nat → Int) : Array Nat :=
  Array.ofFn (n := 24) fun i => clsCoord (act (ellC i))

@[expose] def xiAct (U : Nat → Int) (i : Nat) : Int :=
  (if i % 4 = 0 then -1 else 1) *
    (U i - (U (4 * (i / 4)) + U (4 * (i / 4) + 1) + U (4 * (i / 4) + 2) + U (4 * (i / 4) + 3)) / 2)

@[expose] def permAct (inv : List Nat) (U : Nat → Int) (i : Nat) : Int := U (inv.getD i 0)

@[expose] def signAct (m : Nat) (U : Nat → Int) (i : Nat) : Int := if m.testBit i then -U i else U i

end Cover

@[expose] def Gen.latAct : Gen → (Nat → Int) → Nat → Int
  | .rho _ => fun U => U
  | .perm arr => Cover.permAct (permInv arr).toList
  | .sign a => Cover.signAct (wordN a)
  | .xi => Cover.xiAct
  | .tau => fun U => U

@[expose] def Gen.isVis : Gen → Bool
  | .tau => false
  | g => g.validB

@[expose] def Gen.l2Rows : Gen → Array Nat
  | .perm arr =>
    let inv := (permInv arr).toList
    Cover.rowsOfAct (Cover.permAct inv)
  | .sign a => Cover.rowsOfAct (Cover.signAct (wordN a))
  | .xi => Cover.rowsOfAct Cover.xiAct
  | _ => Cover.rowsOfAct fun U => U

namespace Cover

@[expose] def l2Word (w : List Gen) (v : Nat) : Nat :=
  (w.map Gen.l2Rows).foldl (fun v m => actRows m v) v

@[expose] def wordRows (w : List Gen) : Array Nat :=
  let mats := w.map Gen.l2Rows
  Array.ofFn (n := 24) fun j => mats.foldl (fun v m => actRows m v) ((1 : Nat) <<< j.val)

structure CoverTables where
  lab : ByteArray
  lev : ByteArray
  gen : ByteArray
  par : ByteArray


@[inline, expose] def cvImg (rows : Array (Array Nat)) (g v : Nat) : Nat := actRows rows[g]! v

@[inline, expose] def cvOK (T : CoverTables) (rows : Array (Array Nat)) (seeds : Array Nat)
    (v : Nat) : Bool :=
  let o := rd8 T.lab v
  if o == 0 then true else
    let l := rd8 T.lev v
    o ≤ seeds.size &&
    (if l == 1 then v == seeds[o - 1]! else
      let p := rd32 T.par v
      let g := rd8 T.gen v
      l != 0 && p < 2 ^ 24 && g < 2 && rd8 T.lab p == o && rd8 T.lev p + 1 == l &&
        cvImg rows g p == v) &&
    allFrom (fun j => rd8 T.lab (cvImg rows j v) == o) 0 2

@[expose] def coverCheck (T : CoverTables) (rows : Array (Array Nat)) (seeds sizes : Array Nat)
    (chunks : Nat) : Bool :=
  rows.size == 2 && rows.all (fun m => m.size == 24 && m.all (fun x => x < 2 ^ 24)) &&
  seeds.size == sizes.size && seeds.size < 255 &&
  parAll (2 ^ 24) chunks (cvOK T rows seeds) &&
  countBelow (fun v => rd8 T.lab v != 0) (2 ^ 24) == deltaCount &&
  parAll seeds.size chunks
    (fun r => countBelow (fun v => rd8 T.lab v == r + 1) (2 ^ 24) == sizes[r]!) &&
  allFrom (fun r => seeds[r]! < 2 ^ 24 && rd8 T.lab seeds[r]! == r + 1) 0 seeds.size


end Cover

end CFSG.Monster.AxisCount.Native
