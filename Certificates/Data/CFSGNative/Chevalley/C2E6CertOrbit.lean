module

public import Certificates.Data.CFSGNative.Chevalley.C2E6CertLie
public import Std.Data.HashMap

public section

namespace CFSG.Monster.Existence.StdOdd.CertNative

open CFSG.LieType.Chevalley.C2E6Std.MatrixModel.Native

@[expose] def e7 : Vec := (1 <<< 7, 0)

structure OrbitCert where
  pts : Array Vec
  par : Array Nat
  gen : Array Bool
  nbA : Array Nat
  nbB : Array Nat
  idx : Vec → Nat

def produce (A B : Mat) (e : Vec) : OrbitCert := Id.run do
  let TA := mkTbl A
  let TB := mkTbl B
  let mut pts : Array Vec := #[e]
  let mut par : Array Nat := #[0]
  let mut gen : Array Bool := #[false]
  let mut nbA : Array Nat := #[]
  let mut nbB : Array Nat := #[]
  let mut tbl : Std.HashMap Vec Nat := (∅ : Std.HashMap Vec Nat).insert e 0
  let mut h := 0
  while h < pts.size do
    let u := pts[h]!
    let wa := applyT TA u
    match tbl.get? wa with
    | some j => nbA := nbA.push j
    | none =>
      let j := pts.size
      pts := pts.push wa
      par := par.push h
      gen := gen.push false
      tbl := tbl.insert wa j
      nbA := nbA.push j
    let wb := applyT TB u
    match tbl.get? wb with
    | some j => nbB := nbB.push j
    | none =>
      let j := pts.size
      pts := pts.push wb
      par := par.push h
      gen := gen.push true
      tbl := tbl.insert wb j
      nbB := nbB.push j
    h := h + 1
  return ⟨pts, par, gen, nbA, nbB, fun v => tbl.getD v 0⟩

@[inline, expose] def allStep (j c n : Nat) (p : Nat → Bool) : Bool :=
  Nat.all ((n + c - 1 - j) / c) fun k _ => p (j + c * k)

@[expose] def parAll (n chunks : Nat) (p : Nat → Bool) : Bool :=
  let c := chunks + 1
  ((List.range c).map fun j => Task.spawn fun _ => allStep j c n p).all Task.get


@[expose] def OrbitCert.mem (c : OrbitCert) (u : Vec) : Bool :=
  c.idx u < c.pts.size && c.pts.getD (c.idx u) (0, 0) == u


@[expose] def rhoWith (fm : Vec → Vec → Bool × Bool) (bnz : Vec → Vec → Bool) (mem : Vec → Bool)
    (u w : Vec) : Nat :=
  if u == w then 0 else
    let b := fm u w
    if b.1 || b.2 then 4 else if bnz u w then 3 else if mem (vadd u w) then 1 else 2


@[expose] def rhoT (TF : Array Vec) (BO : Array (List (Nat × Nat))) (mem : Vec → Bool)
    (u w : Vec) : Nat :=
  rhoWith (bformT TF) (bracketNZ BO) mem u w

end CFSG.Monster.Existence.StdOdd.CertNative
