module

public import Certificates.Data.CFSGNative.Fi24.Certificate

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native

set_option compiler.extract_closed false

@[expose] def packedN (O : Enum) : Table :=
  Array.ofFn (n := nPts) fun i => O.par[i.1]! ||| (O.lab[i.1]! <<< 30)

@[expose] def gensN (O : Enum) (l : Nat) : Table := if l = 1 then O.alpha else O.beta

@[expose] def gensInvN (O : Enum) (bInv : Table) (l : Nat) : Table :=
  if l = 1 then O.alpha else bInv

@[expose] def clsAtN (O : Enum) (bInv pl tP : Table) (k : Nat) (q : Array Nat) : Array Nat :=
  applyTree pl (gensN O) k (apT tP (applyTreeInv pl (gensInvN O bInv) k q))

@[expose] def letterJN (L : Array Table) (z : Int) : Table :=
  if 0 < z then L[2 * (z.natAbs - 1)]! else L[2 * (z.natAbs - 1) + 1]!

@[expose] def tPTableN (O : Enum) (tA tB : Table) : Table := Id.run do
  let mut t : Table := Array.replicate nPts 0
  for p in [1:nPts] do
    let q := ap t (ap O.par p)
    let v := if ap O.lab p == 1 then ap tA q else ap tB q
    t := t.set! p (UInt32.ofNat v)
  return t

@[expose] def normWordsN : Array (List Int) := #[
  [1, 4, 8, -13, 9, 3, -10, -5, -5, -8, 5, 5, 12, -8, -8, -8, 13, 8, 7, -12, 13, -10],
  [3, 9, 7, -3, 2, -6, -6, 11, 4, -7, -5, -13, 11, 10, 5, 7, -8, -7, 8, -11, 8, 9, -11, 13, 9,
    13]]

structure Ctx where
  O : Enum
  L : Array Table
  tP : Table
  pl : Table
  bInv : Table

@[expose] def mkCtx (O : Enum) : Ctx :=
  let L := chainLetters O
  ⟨O, L, tPTableN O (wordT nPts (letterJN L) normWordsN[0]!)
    (wordT nPts (letterJN L) normWordsN[1]!), packedN O, invT nPts O.beta⟩

@[expose] def clsPt (c : Ctx) (k p : Nat) : Nat := (clsAtN c.O c.bInv c.pl c.tP k #[p])[0]!

@[expose] def commB (c : Ctx) (k l : Nat) : Bool := clsPt c k l == l


@[expose] def wordTab (c : Ctx) (w : List Nat) : Table :=
  w.foldr (fun l T => compT nPts c.L[l]! T) (idT nPts)


@[expose] def vecOf (c : Ctx) (T : Array Nat) (d : Nat) : Array Bool :=
  let img := clsAtN c.O c.bInv c.pl c.tP d T
  (Array.range T.size).map fun j => img[j]! == T[j]!


@[expose] def iterN (f : Nat → Nat) : Nat → Nat → Nat
  | 0, p => p
  | n + 1, p => iterN f n (f p)

@[expose] def retTime (f : Nat → Nat) (p bound : Nat) : Nat := Id.run do
  let mut q := f p
  let mut t := 1
  for _ in [0:bound] do
    if q == p then return t
    q := f q
    t := t + 1
  return 0

@[expose] def cycOK (f : Nat → Nat) (p L : Nat) : Bool :=
  L % 3 == 0 && L != 0 && iterN f L p == p && iterN f (L / 3) p != p

@[expose] def cyc3 (f : Nat → Nat) (p : Nat) : Bool := cycOK f p (retTime f p 64)


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
