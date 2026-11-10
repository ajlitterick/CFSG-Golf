module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Std.Data.HashMap

public section

namespace CFSG.RuF45

open CFSG.Monster.B.Co2.Native

abbrev Word := List (Nat × Bool)

@[expose] def lettArr (G Gi : Array (Array Nat)) (l : Nat × Bool) : Array Nat :=
  if l.2 then G[l.1]! else Gi[l.1]!

@[expose] def evalArr (n : Nat) (G Gi : Array (Array Nat)) : Word → Array Nat
  | [] => idA n
  | l :: w => compA n (lettArr G Gi l) (evalArr n G Gi w)

@[expose] def decodeWord (s : String) : Word :=
  s.toList.map fun c => ((c.toNat - 48) / 2, (c.toNat - 48) % 2 == 0)

@[expose] def invArrs (n : Nat) (G : Array (Array Nat)) : Array (Array Nat) :=
  G.map (invCand n)

@[expose] def invsOK (n : Nat) (G Gi : Array (Array Nat)) : Bool :=
  G.size == Gi.size && allLt G.size fun i => isInvA n G[i]! Gi[i]!


@[expose] def onLineP (pts : Array Nat) (p v : Nat) : Bool :=
  pts[3 * v]! == p || pts[3 * v + 1]! == p || pts[3 * v + 2]! == p

@[expose] def mkPtL (pts : Array Nat) : Array Nat := Id.run do
  let mut bk : Array (Array Nat) := Array.replicate 1755 #[]
  for v in [0:2925] do
    for k in [0:3] do
      bk := bk.modify pts[3 * v + k]! fun l => l.push v
  let mut out : Array Nat := #[]
  for p in [0:1755] do
    for k in [0:5] do
      out := out.push (bk[p]!)[k]!
  return out


@[expose] def nbrL (pts ptL : Array Nat) (x : Nat) : List Nat :=
  if x < 1755 then (List.range 5).map fun k => ptL[5 * x + k]! + 1755
  else (List.range 3).map fun k => pts[3 * (x - 1755) + k]!

@[expose] def layBFS (pts ptL : Array Nat) (b : Nat) : Array Nat × Array Nat := Id.run do
  let mut lay : Array Nat := (Array.replicate 4680 255).set! b 0
  let mut par : Array Nat := Array.replicate 4680 0
  let mut q : Array Nat := #[b]
  for h in [0:4680] do
    if h < q.size then
      let x := q[h]!
      for y in nbrL pts ptL x do
        if y < 4680 && lay[y]! == 255 then
          lay := lay.set! y (lay[x]! + 1)
          par := par.set! y x
          q := q.push y
  return (lay, par)


@[expose] def lineMapsP (pts g : Array Nat) (v w : Nat) : Bool :=
  (List.range 3).all fun k => onLineP pts g[pts[3 * v + k]!]! w

@[expose] def actOK (pts g : Array Nat) (y x : Nat) : Bool :=
  if y < 1755 then decide (x < 1755) && g[y]! == x
  else decide (1755 ≤ x) && decide (x < 4680) && lineMapsP pts g (y - 1755) (x - 1755)


end CFSG.RuF45
