module

public import Certificates.Data.SmithL6Check

public section

namespace CFSG.SmithL6

open CFSG.SmithE (applyCols)


@[expose] def ugens : Array Nat := #[189, 193, 201, 158, 162, 170, 127, 131, 139]

@[expose] def uco : Array Nat := #[9, 18, 27, 36, 45, 54, 63, 65, 130, 195, 260, 325, 390, 455, 72,
  144, 216, 288, 360, 432, 504, 73, 146, 219, 292, 365, 438, 511, 64, 128, 192, 256, 320, 384, 448,
  8, 16, 24, 32, 40, 48, 56, 1, 2, 3, 4, 5, 6, 7]

@[expose] def uaWord (a x : Nat) : Nat :=
  (List.range 9).foldr (fun j y => if a.testBit j then tvTab[ugens[j]!]![y]! else y) x

@[expose] def chkUa : Bool :=
  let P0 := planePtsArr[0]!
  ugens.size == 9 && uco.size == 49 && ugens.all (fun g => decide (g < 1953) && inPlane 0 g) &&
  (List.range 49).all (fun k => decide (0 < uco[k]!) && decide (uco[k]! < 512) &&
    (List.range k).all fun l => uco[l]! != uco[k]!) &&
  P0.all (fun p => P0.all fun q => tvTab[p]![q]! == q) &&
  (List.range 49).all (fun k => (List.range 1953).all fun x =>
    uaWord uco[k]! x == tvTab[P0[k]!]![x]!) &&
  (List.range 512).all (fun a => a == 0 || (List.range 1953).any fun x => uaWord a x != x) &&
  (List.range 1953).all (fun q => !(P0.all fun p => tvTab[p]![q]! == q) || inPlane 0 q) &&
  (List.range 1395).all fun j => j == 0 || P0.any fun p => planeImg p j != j

@[expose] def elemGens : Array Nat :=
  ((List.range 6).flatMap fun i => (List.range 6).filterMap fun j =>
    if i == j then none else some tvIdxTab[64 * 2 ^ i + 2 ^ j]!).toArray

@[expose] def stabGens : Array Nat := ((List.range 1953).filter fun p => planeImg p 0 == 0).toArray


@[expose] def dRoot (c : Nat) : Nat := ((List.range 1395).find? fun j => meetCard 0 j == c).getD 0


@[expose] def uSums : Array Bool :=
  Array.ofFn (n := 512) fun v => (List.range 49).any fun k => (List.range 49).any fun l =>
    k != l && uco[k]! ^^^ uco[l]! == v.val

@[expose] def uCls (S2 : Array Bool) (v : Nat) : Nat :=
  if v == 0 then 0 else if uco.contains v then 1 else if S2[v]! then 2 else 3

@[expose] def uRoot (S2 : Array Bool) (c : Nat) : Nat :=
  ((List.range 512).find? fun v => uCls S2 v == c).getD 0

@[expose] def pos0 (q : Nat) : Nat := planePtsArr[0]!.findIdx (· == q)

@[expose] def ucols (p : Nat) : Array Nat :=
  Array.ofFn (n := 9) fun j => uco[pos0 tvTab[p]![ugens[j.val]!]!]!


end CFSG.SmithL6
