module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8Wr

open CFSG.QuasithinUnique.A6Facts

@[expose] def c0 (i : Nat) : List Nat := Core.p0Lit.getD i []

@[expose] def t0 (a b : Nat) : Nat := Core.p0Lit.idxOf (Core.cmul (c0 a) (c0 b))

@[expose] def i0 : Nat := Core.p0Lit.idxOf Core.cid

@[expose] def mtab (_ : Unit := ()) : Array Nat :=
  Array.ofFn (n := 1024) fun k => t0 (k.val / 32) (k.val % 32)

@[expose] def mulI (M : Array Nat) (x y : Nat × Nat × Bool) : Nat × Nat × Bool :=
  if x.2.2 then (M.getD (x.1 * 32 + y.2.1) 0, M.getD (x.2.1 * 32 + y.1) 0, !y.2.2)
  else (M.getD (x.1 * 32 + y.1) 0, M.getD (x.2.1 * 32 + y.2.1) 0, y.2.2)

@[expose] def oneI : Nat × Nat × Bool := (i0, i0, false)


@[expose] def p0Ok (_ : Unit := ()) : Bool :=
  (List.range 32).all (fun a => (List.range 32).all fun b =>
    Core.p0Lit.contains (Core.cmul (c0 a) (c0 b))) &&
    Core.p0Lit.contains Core.cid && (c0 i0 == Core.cid)


end CFSG.EvenSporadicStandard.Fin76b.TS8Wr
