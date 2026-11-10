module

public import Certificates.Data.CFSGNative.Co1.Odd

public section

namespace CFSG.Sporadic.Co1.CoTwoNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Co1.OddNative

@[expose] def actN (R : Array Nat) (x : Nat) : Nat := vecMulN 24 (transposeRows 24 R) x

structure OTree where
  pts : Array Nat
  par : Array Nat
  lab : Array Nat
deriving Inhabited

def orbitTreeBFS (rr : Nat → Array Nat) (lv : List Nat) (b : Nat) : OTree := Id.run do
  let ts : Array (Array Nat) := (lv.map fun l => transposeRows 24 (rr l)).toArray
  let ls : Array Nat := lv.toArray
  let mut pos : Array UInt32 := Array.replicate (1 <<< 24) none32
  let mut pts : Array Nat := #[b]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  pos := pos.set! b 0
  let mut h := 0
  while h < pts.size do
    let x := pts[h]!
    for t in [0:ts.size] do
      let y := vecMulN 24 ts[t]! x
      if pos[y]! == none32 then
        pos := pos.set! y (UInt32.ofNat pts.size)
        pts := pts.push y
        par := par.push h
        lab := lab.push ls[t]!
    h := h + 1
  return ⟨pts, par, lab⟩

@[expose] def otreeOK (rr : Nat → Array Nat) (lv : List Nat) (b : Nat) (T : OTree) : Bool :=
  let n := T.pts.size
  let pos := posTable 24 T.pts
  decide (0 < n) && T.par.size == n && T.lab.size == n && T.pts[0]! == b &&
    allIn 0 n fun k => decide (T.pts[k]! < 2 ^ 24) && (pos[T.pts[k]!]!).toNat == k &&
      (k == 0 || (decide (T.par[k]! < k) && lv.contains T.lab[k]! &&
        T.pts[k]! == actN (rr T.lab[k]!) T.pts[T.par[k]!]!))

@[expose] def treeSize (rr : Nat → Array Nat) (lv : List Nat) (b : Nat) : Nat :=
  let T := orbitTreeBFS rr lv b
  if otreeOK rr lv b T then T.pts.size else 0


@[expose] def fixOK (rr : Nat → Array Nat) (x s : Nat) : Bool := actN (rr s) x == x


end CFSG.Sporadic.Co1.CoTwoNative
