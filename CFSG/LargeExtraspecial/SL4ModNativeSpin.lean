module

public import CFSG.LargeExtraspecial.SL4ModNativeCosets

public section

namespace CFSG.LargeExtraspecial.SL4Mod.Native

open CFSG.Sporadic.SmallF2.Native

set_option compiler.extract_closed false

@[expose] def actV (t : Array Nat) (x : Nat) : Nat :=
  ofBits 105 fun k => x.testBit (t[k]! % 105)

@[expose] def xorSel (mask : Nat) (L : Array Nat) : Nat :=
  (List.range L.size).foldl (fun acc t => if mask.testBit t then acc ^^^ L[t]! else acc) 0

@[expose] def nz (x : Nat) : Bool := (x &&& (2 ^ 105 - 1)) != 0

@[expose] def inSpan (x : Nat) (B : Array Nat) : Bool :=
  (List.range (2 ^ B.size)).any fun mask => xorSel mask B == x

@[expose] def indep9 (L : Array Nat) : Bool :=
  (List.range 512).all fun mask => mask == 0 || nz (xorSel mask L)

@[expose] def derivOK (taus : Array (Array Nat)) (m : Nat) (L : Array Nat)
    (src : Array (Nat × Nat)) : Bool :=
  L[0]! == m && (List.range L.size).all fun t => t == 0 ||
    (decide (src[t]!.1 < 6) && decide (src[t]!.2 < t) &&
      L[t]! == actV taus[src[t]!.1]! L[src[t]!.2]!)

@[expose] def closedOK (taus : Array (Array Nat)) (B : Array Nat) : Bool :=
  (List.range B.size).all fun t => (List.range 6).all fun s => inSpan (actV taus[s]! B[t]!) B

structure SpinCert where
  L : Array Nat
  src : Array (Nat × Nat)
  big : Bool
  sel : Nat
  B : Array Nat
deriving Inhabited

@[expose] def valid (taus : Array (Array Nat)) (m : Nat) (c : SpinCert) : Bool :=
  derivOK taus m c.L c.src &&
    (if c.big then decide (9 ≤ c.L.size) && indep9 c.L
    else nz (xorSel c.sel c.L) && decide (c.B.size ≤ 7) && inSpan (xorSel c.sel c.L) c.B &&
      closedOK taus c.B)


structure OrbData where
  par : Array Nat
  lab : Array Nat
  orep : Array Nat
deriving Inhabited

@[expose] def orbGens (i : Nat) : List Nat := [0, 1, 2, i + 3]


@[expose] def iterPar (par : Array Nat) : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => iterPar par n (par[k]! % 105)

@[expose] def checkOrb (d : CosetData) (i : Nat) (od : OrbData) : Bool :=
  (List.range 105).all fun k =>
    (od.par[k]! % 105 == k ||
        (orbGens i).any fun s => od.par[k]! % 105 == d.tau[s]![k]! % 105) &&
      decide (od.lab[k]! < 7) && iterPar od.par 105 k == od.orep[od.lab[k]!]! % 105

@[expose] def expand (od : OrbData) (c : Nat) : Nat :=
  ofBits 105 fun k => c.testBit od.lab[k]!


end CFSG.LargeExtraspecial.SL4Mod.Native
