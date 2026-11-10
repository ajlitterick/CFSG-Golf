module

public import Certificates.Data.SmithL6Check

public section

namespace CFSG.SmithL6

@[expose] def stabCls (a : Nat) : Nat :=
  if a = 0 then 0 else
  if (tvPair a).1 = (tvPair 0).1 then 1 else
  if (tvPair a).2 = (tvPair 0).2 then 2 else
  3 + 2 * (if form (tvPair 0).2 (tvPair a).1 then 1 else 0) +
    (if form (tvPair a).2 (tvPair 0).1 then 1 else 0)


@[expose] def stabReps : Array Nat :=
  (Array.range 7).map fun c => ((List.range 1953).find? fun a => stabCls a == c).getD 0

@[expose] def stabRep (c : Nat) : Nat := stabReps[c]!


@[expose] def stabSizes : List Nat := [1, 30, 30, 420, 480, 480, 512]

@[expose] def chkStabCard : Bool :=
  (List.range 7).all fun c =>
    ((List.range 1953).filter fun a => stabCls a == c).length == stabSizes[c]!

@[expose] def chkStabComm : Bool :=
  let A := (List.range 1953).filter fun a => decide (stabCls a ≤ 1)
  let B := (List.range 1953).filter fun a => stabCls a == 0 || stabCls a == 2
  A.all (fun a => A.all fun b => tvImg a b == b) && B.all (fun a => B.all fun b => tvImg a b == b) &&
    tvImg 1 0 == 0 && tvImg 94 0 == 0 && tvImg 1 94 != 94

end CFSG.SmithL6
