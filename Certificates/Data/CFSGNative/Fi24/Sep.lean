module

public import Certificates.Data.CFSGNative.Fi24.Core

public section

namespace CFSG.Sporadic.Fi24.Native

@[expose] def zeroW (d : Nat) : Array W := Array.replicate d W.zero

@[expose] def addW (d : Nat) (X Y : Array W) : Array W :=
  Array.ofFn (n := d) fun i => (X[i.val]?.getD W.zero).add (Y[i.val]?.getD W.zero)


@[expose] def prodW (d : Nat) (mats : Array (Array W)) (word : List Nat) : Array W :=
  word.foldl (fun M x => mulW M (mats[x]?.getD #[])) (idW d)


@[expose] def projW (d : Nat) (v : W) (k : Nat) : Array W :=
  Array.ofFn (n := d) fun i =>
    (W.zero.setTrit i.val 1).sub (W.zero.setTrit k (v.trit i.val))


@[expose] def canonRows (d : Nat) (X : Array W) : Bool := X.size == d && X.all W.canon

@[expose] def eqRows (d : Nat) (X Y : Array W) : Bool := X.size == d && decide (X = Y)


@[expose] def invW (d : Nat) (M : Array W) : Array W := Id.run do
  let mut a := M
  let mut b := idW d
  for c in [0:d] do
    let l := c >>> 6
    let bit : UInt64 := (1 : UInt64) <<< (c &&& 63).toUInt64
    let mut p := d
    for i in [c:d] do
      if p == d && a[i]!.nz l bit then p := i
    if p < d then
      a := a.swapIfInBounds c p
      b := b.swapIfInBounds c p
      if a[c]!.limbM l &&& bit != 0 then
        a := a.modify c W.neg
        b := b.modify c W.neg
      let pa := a[c]!
      let pb := b[c]!
      for i in [0:d] do
        if i != c then
          let x := a[i]!
          if x.limbP l &&& bit != 0 then
            a := a.modify i (·.sub pa)
            b := b.modify i (·.sub pb)
          else if x.limbM l &&& bit != 0 then
            a := a.modify i (·.add pa)
            b := b.modify i (·.add pb)
  return b

@[expose] def sepP (w : Array W) (v : W) (k : Nat) : Array W := Id.run do
  let Q := projW 781 v k
  for i in [0:781] do
    let w' := w.modify i fun x => x.add (W.zero.setTrit k 1)
    let wi := invW 781 w'
    if eqRows 781 (mulW wi w') (idW 781) then return mulW Q wi
  return zeroW 781

@[expose] def gramW (r : Nat) (R F : Array W) : Array W := mulW (mulW R F) (transposeW r 781 R)

@[expose] def orthoProj (r : Nat) (R F S : Array W) : Array W :=
  mulW (transposeW r 781 R) (mulW S (mulW R F))

end CFSG.Sporadic.Fi24.Native
