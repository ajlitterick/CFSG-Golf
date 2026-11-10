module

public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.SectionRank.Native

structure Local3Data (m : Nat) where
  seedA : String
  seedB : String
  oA : Nat
  oB : Nat
  defs : List (List Nat)
  gens : List (List Nat)
  ords : List Nat
  rels : List (List (Fin m × Bool))
  masks : String
  n : Nat

@[expose] def ofCodes (m : Nat) [NeZero m] (c : List Nat) : List (Fin m × Bool) :=
  c.map (fun x =>
    (⟨x / 2 % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩, decide (x % 2 = 0)))

section Native

variable {M V : Type} [Inhabited M] (O : Ops M V)


@[expose] def invCodes (w : List Nat) : List Nat := w.reverse.map (· ^^^ 1)


@[expose] def defsOK : Nat → List (List Nat) → Bool
  | _, [] => true
  | n, w :: ws => w.all (fun c => decide (c < n)) && defsOK (n + 2) ws


@[expose] def strictInc : List Nat → Bool
  | a :: b :: l => decide (a < b) && strictInc (b :: l)
  | _ => true


end Native

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
