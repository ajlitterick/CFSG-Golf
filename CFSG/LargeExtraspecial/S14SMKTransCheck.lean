module

public import CFSG.LargeExtraspecial.SMod20BasicCheck
public import Certificates.Data.SMod20UaStab
public import Std.Data.HashMap.Basic

public section

namespace CFSG.SmithE

open CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def frobC (c : Nat) : Nat :=
  (List.range 6).foldl (fun acc i => acc + f4mul (coord c i) (coord c i) * 4 ^ i) 0

@[expose] def dltC (c : Nat) : Nat :=
  (List.range 6).foldl (fun acc i => acc + (if i < 2 then f4mul 2 (coord c i) else coord c i) *
    4 ^ i) 0

@[expose] def ptMapT (f : Nat → Nat) : Array Nat :=
  Array.ofFn (n := 693) fun p => uPos[normC (f uPts[p.val]!)]!

@[expose] def compTab (s t : Array Nat) : Array Nat := Array.ofFn (n := 693) fun x => s[t[x.val]!]!

@[expose] def invTab (s : Array Nat) : Array Nat :=
  (List.range 693).foldl (fun r x => r.set! s[x]! x) (Array.replicate 693 0)

@[expose] def idTab : Array Nat := Array.ofFn (n := 693) fun x => x.val

@[expose] def stabTab (T : Array Table) (g : Nat) : Array Nat :=
  Array.ofFn (n := 693) fun x => stabAp T stabWords[g]! x.val

@[expose] def liftTab (T : Array Table) : Nat → Array Nat
  | 0 => idTab
  | 1 => stabTab T 0
  | 2 => ptMapT frobC
  | 3 => compTab (compTab (ptMapT dltC) (ptMapT frobC)) (invTab (ptMapT dltC))
  | _ => compTab (compTab (compTab (ptMapT dltC) (ptMapT dltC)) (ptMapT frobC))
      (invTab (compTab (ptMapT dltC) (ptMapT dltC)))

@[expose] def invPairOK (t r : Array Nat) : Bool :=
  allIn 0 693 fun x => decide (t[x]! < 693) && decide (r[x]! < 693) && r[t[x]!]! == x &&
    t[r[x]!]! == x

@[expose] def normOK (T : Array Table) (s : Array Nat) : Bool :=
  allIn 0 693 fun p => allIn 0 693 fun x => s[ap T[p]! x]! == ap T[s[p]!]! s[x]!

@[expose] def sArrT (W0 s : Array Nat) : Array Nat :=
  Array.ofFn (n := 21) fun k => uaPos W0 s[W0[k.val]!]!

@[expose] def key21 (s : Array Nat) : Nat := s.foldl (fun acc x => acc * 32 + x) 0


@[expose] def xorSel : List Nat → Nat → Nat
  | [], _ => 0
  | b :: bs, m => (if m % 2 = 1 then b else 0) ^^^ xorSel bs (m / 2)

@[expose] def indepOK (bs : List Nat) : Bool :=
  allIn 0 (2 ^ bs.length) fun m => allIn 0 (2 ^ bs.length) fun m' =>
    m == m' || xorSel bs m % 2 ^ 20 != xorSel bs m' % 2 ^ 20

@[expose] def echRed (E : List (Nat × Nat)) (v : Nat × Nat) : Nat × Nat :=
  E.foldl (fun w e => if w.1 ^^^ e.1 < w.1 then (w.1 ^^^ e.1, w.2 ^^^ e.2) else w) v

@[expose] def echIns (E : List (Nat × Nat)) (w : Nat × Nat) : List (Nat × Nat) :=
  (E.filter fun e => e.1 > w.1) ++ [w] ++ E.filter fun e => e.1 < w.1

@[expose] def echOf (vs : List Nat) : List (Nat × Nat) × List Nat :=
  (vs.zipIdx).foldl (fun st vj =>
    let w := echRed st.1 (vj.1, 2 ^ vj.2)
    if w.1 == 0 then (st.1, st.2 ++ [w.2]) else (echIns st.1 w, st.2)) ([], [])

@[expose] def maskOf (E : List (Nat × Nat)) (v : Nat) : Nat := (echRed E (v, 0)).2

@[expose] def pickIndep (vs : List Nat) (k : Nat) : List Nat :=
  (vs.foldl (fun st v =>
    if st.2.length ≥ k then st else
    let w := echRed st.1 (v, 0)
    if w.1 == 0 then st else (echIns st.1 w, st.2 ++ [v])) (([] : List (Nat × Nat)), [])).2

@[expose] def candT (T : Array Table) (W0 s : Array Nat) (a : Nat) : Array Nat :=
  Array.ofFn (n := 693) fun x => uaAp T W0 a 9 s[x.val]!

@[expose] def isInvoT (c : Array Nat) : Bool := allIn 0 693 fun x => c[c[x]!]! == x


@[expose] def sigT (F : Array (Array Bool)) (PP P : Array (Array Nat)) (c : Array Nat) :
    Array Nat :=
  Array.ofFn (n := 891) fun i => uaPlaneOf F PP fun m => c[P[i.val]![m]!]!


@[expose] def dVec (W sg : Array Nat) (i : Nat) : Nat := W[sg[i]!]! ^^^ W[i]!

@[expose] def fixL (c : Array Nat) : List Nat := (List.range 693).filter fun x => c[x]! == x


end CFSG.SmithE
