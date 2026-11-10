module

public import Certificates.Data.CFSGNative.MonsterVis.Frame
public import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Monster.Existence.CoPair.Native

open CFSG.Monster.VisCert.Native

set_option compiler.extract_closed false

@[inline, expose] def letterRows (l : Nat) : Array Nat :=
  (CFSG.Monster.B.Co2.Native.genRecords[l]!).matrix

@[expose] def actLetters : List Nat → Nat → Nat
  | [], v => v
  | l :: w, v => actLetters w (actRows (letterRows l) v)

@[expose] def xWordN (_ : Unit := ()) : List Nat :=
  [5, 16, 1, 15, 5, 16, 1, 15, 5, 16, 1, 15, 5, 16, 1, 15, 5, 16, 1, 15]

@[expose] def yWordN (_ : Unit := ()) : List Nat :=
  [23, 1, 23, 1, 23, 1, 16, 6, 19, 23, 16, 6, 19, 23, 16, 6, 19, 23, 16, 6,
    19, 23, 23, 1]

@[expose] def actXY : List Nat → Nat → Nat
  | [], v => v
  | g :: w, v => actXY w (actLetters (if g == 0 then xWordN else yWordN) v)

@[inline, expose] def genXY (g v : Nat) : Nat := actXY [g] v

structure OrbTables where
  lev : ByteArray
  lab : ByteArray
  par : ByteArray


@[inline, expose] def orbPoint (seed : Nat) (lev par lab : Nat → Nat) (v : Nat) : Bool :=
  let l := lev v
  if l == 0 then true else
    (if l == 1 then v == seed else
      let p := par v
      let g := lab v
      p < 2 ^ 24 && g < 2 && lev p + 1 == l && genXY g p == v) &&
    genXY 0 v < 2 ^ 24 && lev (genXY 0 v) != 0 && genXY 1 v < 2 ^ 24 && lev (genXY 1 v) != 0

@[expose] def orbCheck (seed N : Nat) (T : OrbTables) (chunks : Nat) : Bool :=
  seed < 2 ^ 24 && rd8 T.lev seed == 1 &&
    parAll (2 ^ 24) chunks (orbPoint seed (rd8 T.lev) (rd32 T.par) (rd8 T.lab)) &&
    countBelow (fun v => rd8 T.lev v != 0) (2 ^ 24) == N


@[inline, expose] def wr16 (b : ByteArray) (i x : Nat) : ByteArray :=
  (b.set! (2 * i) (UInt8.ofNat x)).set! (2 * i + 1) (UInt8.ofNat (x >>> 8))


end CFSG.Monster.Existence.CoPair.Native
