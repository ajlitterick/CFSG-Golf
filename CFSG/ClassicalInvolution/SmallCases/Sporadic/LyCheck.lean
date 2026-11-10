module

public import Certificates.Data.CFSGNative.Ly.Certificate
public import Certificates.Data.CFSGNative.Perm.Chain
public import Certificates.Data.CFSGNative.Co1.Involutions
public import Std.Data.HashSet
public meta import Certificates.Data.CFSGNative.Ly.Certificate
public meta import Certificates.Data.CFSGNative.Perm.Chain
public meta import Certificates.Data.CFSGNative.Co1.Involutions

public section

namespace CFSG.ClassicalInvolution

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Ly.Native

namespace LyProof

@[expose] def applyL (L : Array Table) (w : List Nat) (p : Nat) : Nat :=
  w.foldr (fun l q => ap L[l]! q) p


@[expose] def invW (w : List Nat) : List Nat := w.reverse.map CFSG.Perm.Native.invL

@[expose] def packL (l : List Nat) : Nat := l.foldr (fun v acc => v + 16777216 * acc) 0


@[expose] def fixL (n : Nat) (T : Table) : List Nat := (List.range n).filter fun p => ap T p == p


@[expose] def conjImg (L : Array Table) (Tz : Table) (path : List Nat) (p : Nat) : Nat :=
  applyL L path (ap Tz (applyL L (invW path) p))

@[expose] def conjKey (L : Array Table) (Tz : Table) (path : List Nat) : Nat :=
  packL [conjImg L Tz path 3, conjImg L Tz path 1]


@[expose] def conjOK (L : Array Table) (Tz : Table) (paths : Array (List Nat)) : Bool :=
  decide (paths.size = 406875) && paths.all (fun p => p.all fun l => decide (4 ≤ l ∧ l ≤ 7)) &&
    CFSG.Sporadic.Co1.InvNative.distinctKeys (paths.toList.map (conjKey L Tz))


@[expose] def tyOf (n : Nat) (Tks : Array Table) : Table :=
  compT n Tks[1]! (compT n Tks[0]! (compT n Tks[1]! (compT n Tks[0]! Tks[1]!)))

@[expose] def commOK (n : Nat) (Tz : Table) (Tks : Array Table) : Bool :=
  let Ty := tyOf n Tks
  chainQ.all fun q => ap Ty (ap Ty q) == q &&
    ap Tks[0]! (ap Ty (ap Tks[0]! (ap Ty q))) == ap Tz q

@[expose] def piOf (Fl masks : Array Nat) (p : Nat) : Nat :=
  masks[(Fl.findIdx? fun x => x == p).getD 0]!


@[expose] def predB1 (i b : Nat) : Bool := decide ((b + 11 - i) % 11 < 5)

@[expose] def predB2 (i b : Nat) : Bool :=
  b == i || decide (5 ≤ (b + 11 - i) % 11 ∧ (b + 11 - i) % 11 < 9)

@[expose] def witOK (Fl masks : Array Nat) : Bool :=
  (List.range 11).all fun i =>
    (Fl.any fun p => (List.range 11).all fun b => (piOf Fl masks p).testBit b == predB1 i b) &&
      (Fl.any fun p => (List.range 11).all fun b => (piOf Fl masks p).testBit b == predB2 i b)


@[expose] def sKey (Ts : Array Table) (path : List Nat) : Nat :=
  packL (chainQ.toList.map fun q => applyL Ts path q)


@[expose] def sOK (Ts : Array Table) (paths : Array (List Nat)) : Bool :=
  let keys := paths.toList.map (sKey Ts)
  decide (paths.size = 256) && paths[0]! == [] && Ts.size == 3 &&
    paths.all (fun p => p.all fun g => decide (g < 3)) &&
    CFSG.Sporadic.Co1.InvNative.distinctKeys keys &&
    paths.all fun p => [0, 1, 2].all fun g => keys.contains (sKey Ts (p ++ [g]))

@[expose] def isInvolP (Ts : Array Table) (p : List Nat) : Bool :=
  chainQ.all (fun q => applyL Ts (p ++ p) q == q) && !(chainQ.all fun q => applyL Ts p q == q)

@[expose] def dMap (L : Array Table) (Tz : Table) (Ts : Array Table) (pj r : List Nat)
    (p : Nat) : Nat :=
  applyL L r (ap Tz (applyL L (invW r) (applyL Ts pj p)))

@[expose] def iterD (d : Nat → Nat) : Nat → Nat → Nat
  | 0, p => p
  | m + 1, p => iterD d m (d p)

@[expose] def coverEq (L : Array Table) (Tz : Table) (Ts : Array Table) (pj r : List Nat)
    (m : Nat) : Bool :=
  chainQ.all fun q =>
    applyL Ts pj (iterD (dMap L Tz Ts pj r) m (applyL L r q)) ==
      iterD (dMap L Tz Ts pj r) m (applyL L r (ap Tz q))


@[expose] def ordD (d : Nat → Nat) (bound : Nat) : Nat := Id.run do
  let mut cur := chainQ.toList
  for k in [1:bound + 1] do
    cur := cur.map d
    if cur == chainQ.toList then return k
  return 0


@[expose] def coverOK (L : Array Table) (Tz : Table) (Ts : Array Table) (paths : Array (List Nat))
    (cov : Array (List Nat × Nat)) : Bool :=
  (List.range paths.size).all fun j =>
    !isInvolP Ts paths[j]! ||
      ((cov[j]!).1.all (fun l => decide (l < 12)) && coverEq L Tz Ts paths[j]! cov[j]!.1 cov[j]!.2)


end LyProof

end CFSG.ClassicalInvolution
