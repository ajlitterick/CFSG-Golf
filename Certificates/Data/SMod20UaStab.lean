module

public import Certificates.Data.SMod20CollCheck

public section

namespace CFSG.SmithE

open CFSG.Fischer.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def stabWords : Array (Nat × Nat) := #[(1, 13), (28, 470), (219, 691), (470, 661),
  (14, 692), (220, 235), (441, 662), (10, 231), (209, 244), (430, 452), (4, 447), (20, 436),
  (226, 431), (5, 22), (22, 653), (228, 246), (467, 670), (26, 31), (227, 237), (448, 674),
  (19, 240), (213, 434), (434, 461), (8, 656), (41, 464), (247, 460), (15, 36), (35, 678),
  (241, 442), (463, 684), (24, 224), (229, 445), (450, 687), (61, 383)]

@[expose] def stabAp (T : Array Table) (w : Nat × Nat) (x : Nat) : Nat := ap T[w.1]! (ap T[w.2]! x)

@[expose] def stabSig (T : Array Table) (W : Array Nat) (w : Nat × Nat) : Array Nat :=
  Array.ofFn (n := 21) fun k => uaPos W (stabAp T w W[k.val]!)

@[expose] def uaCls (S2 : Array Bool) (v : Nat) : Nat :=
  if v == 0 then 0 else if uaMem uaCo v then 1 else if S2[v]! then 2 else 3

@[expose] def uaRoot : Nat → Nat
  | 1 => 1
  | 2 => 3
  | 3 => 19
  | _ => 0


@[expose] def uaPtPlanes (P : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut r : Array (Array Nat) := Array.replicate 693 #[]
  for i in [0:891] do
    for k in [0:21] do
      let p := P[i]![k]!
      r := r.set! p (r[p]!.push i)
  return r

@[expose] def uaFlags (P : Array (Array Nat)) : Array (Array Bool) :=
  Array.ofFn (n := 891) fun j => Array.ofFn (n := 693) fun q => uaMem P[j.val]! q.val

@[expose] def uaPlaneOf (F : Array (Array Bool)) (PP : Array (Array Nat)) (img : Nat → Nat) :
    Nat :=
  ((PP[img 0]!).toList.find? fun j => F[j]![img 1]! && F[j]![img 4]!).getD 891

@[expose] def uaMeet (W0 W : Array Nat) : Nat := (List.range 21).countP fun k => uaMem W0 W[k]!

@[expose] def uaDRoot (P : Array (Array Nat)) (c : Nat) : Nat :=
  ((List.range 891).find? fun j => uaMeet P[0]! P[j]! == c).getD 0


end CFSG.SmithE
