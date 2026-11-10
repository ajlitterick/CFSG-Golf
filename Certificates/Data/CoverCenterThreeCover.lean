module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import Certificates.Data.CFSGNative.SectionRank.LocalDet
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestCover

public section

namespace CFSG.SectionRank.Native

open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest

set_option compiler.extract_closed false

structure CoverData (m : Nat) where
  seedA : String
  seedB : String
  nregs : Nat
  prog : List Op
  gens : List Nat
  invExp : List Nat
  e : Fin m → Nat
  cw : Fin m → List (Fin m × Bool) × List (Fin m × Bool)
  rels : List (List (Fin m × Bool))

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def evalWordN [Inhabited M] {m : Nat} (G I : Array M) : List (Fin m × Bool) → M
  | [] => O.one
  | x :: w => O.mul (if x.2 then G[x.1.val]! else I[x.1.val]!) (evalWordN G I w)

@[expose] def coverGens [Inhabited M] {m : Nat} (D : CoverData m) : Array M :=
  let R := O.regsOf D.seedA D.seedB D.nregs D.prog
  (D.gens.map fun r => R[r]!).toArray

@[expose] def coverInvs [Inhabited M] {m : Nat} (D : CoverData m) : Array M :=
  let R := O.regsOf D.seedA D.seedB D.nregs D.prog
  ((D.gens.zip D.invExp).map fun p => O.pow R[p.1]! (p.2 - 1)).toArray

@[expose] def coverCheck [Inhabited M] {m : Nat} (D : CoverData m) : Bool :=
  let G := O.coverGens D
  let I := O.coverInvs D
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && decide (D.gens.length = m) &&
    decide (D.invExp.length = m) && D.gens.all (fun r => decide (r < D.nregs)) &&
    (List.finRange m).all (fun i =>
      decide (0 < D.invExp[i.val]!) && O.eq (O.pow G[i.val]! D.invExp[i.val]!) O.one &&
        (if D.e i = 0 then O.eq G[i.val]! (O.evalWordN G I (commW (D.cw i).1 (D.cw i).2))
          else O.eq (O.pow G[i.val]! (D.e i)) O.one)) &&
    D.rels.all fun w => O.eq (O.evalWordN G I w) O.one


@[expose] def orbitVecs [Inhabited M] [Inhabited V] (gens : Array M) (t : Nat)
    (par lab : Array Nat) (n : Nat) : Array V :=
  (List.range n).foldl (fun W i =>
    if i = 0 then W.push (O.unit t) else W.push (O.vmul W[par[i]!]! gens[lab[i]!]!)) #[]


@[expose] def strictInc : List Nat → Bool
  | a :: b :: l => decide (a < b) && strictInc (b :: l)
  | _ => true

@[expose] def orbitOK [Inhabited M] [Inhabited V] (gens : Array M) (t n : Nat) (key : V → Nat)
    (par lab : Array Nat) : Bool :=
  par.size == n && lab.size == n && decide (0 < n) &&
    (List.range n).all (fun i =>
      i == 0 || (decide (par[i]! < i) && decide (lab[i]! < gens.size))) &&
    strictInc (((O.orbitVecs gens t par lab n).toList.map key).mergeSort fun a b => decide (a ≤ b))


end Ops

end CFSG.SectionRank.Native
