module

public import Certificates.Data.CFSGNative.ExcCensus.Check
public import Std.Data.HashMap

public section

open Std

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

set_option compiler.extract_closed false

@[expose] def imgN (T : Tabs) (r u c : Nat) : Nat :=
  Nat.fold r (fun t _ acc => if c.testBit t then acc ||| 1 <<< T.rt[u]![t]! else acc) 0

@[expose] def closN (T : Tabs) (d r c : Nat) : Nat :=
  Nat.fold (3 ^ d) (fun v _ acc => if subN c T.zm[v]! then acc &&& T.zm[v]! else acc) (2 ^ r - 1)

@[expose] def growC (T : Tabs) (d r c : Nat) : Nat :=
  Nat.repeat (growN T r (closN T d r c)) r c

structure SatW where
  b : Array Nat
  e : Int
  n : Array (Array Int)
  k : Array Nat
  B : Array (Array Int)
  deriving Inhabited

structure A8W where
  b : Array Nat
  span : Array (Nat × Nat × Bool)
  cz : Nat
  hyp : Array (Nat × List (Nat × Nat))
  deriving Inhabited


@[expose] def factorOK (T : Tabs) (r D : Nat) (Q P : Array (Array Int)) : Bool :=
  Nat.all r fun i _ => Nat.all r fun j _ =>
    T.pair[i]![j]! == Nat.fold D (fun k _ s => s + Q[i]![k]! * P[j]![k]!) 0

@[expose] def satOK (T : Tabs) (r D : Nat) (P : Array (Array Int)) (c : Nat) (w : SatW) : Bool :=
  let ρ := w.b.size
  (Nat.all ρ fun a _ => decide (w.b[a]! < r) && c.testBit w.b[a]!) && w.e % 3 != 0 &&
    (Nat.all r fun i _ => !c.testBit i || Nat.all D fun kk _ =>
      w.e * P[i]![kk]! == Nat.fold ρ (fun a _ s => s + w.n[i]![a]! * P[w.b[a]!]![kk]!) 0) &&
    (Nat.all ρ fun a _ => decide (w.k[a]! < r)) &&
    invOK ρ (fun a a' => T.pair[w.k[a]!]![w.b[a']!]!) w.B

@[expose] def chainGramN (a a' : Nat) : Int :=
  if a = a' then 2 else if a + 1 = a' ∨ a' + 1 = a then -1 else 0

@[expose] def chainSumN (Q : Array (Array Int)) (b : Array Nat) (a a' k : Nat) : Int :=
  Nat.fold 8 (fun s _ acc => if a ≤ s ∧ s < a' then acc + Q[b[s]!]![k]! else acc) 0

@[expose] def chainExpN (T : Tabs) (b : Array Nat) (t : Nat) : Int :=
  Nat.fold 8 (fun a _ acc => acc + ((a + 1 : Nat) : Int) * T.pair[t]![b[a]!]!) 0

@[expose] def a8OK (T : Tabs) (d r D : Nat) (Q : Array (Array Int)) (c : Nat) (w : A8W) : Bool :=
  (Nat.all 8 fun a _ => decide (w.b[a]! < r) && c.testBit w.b[a]!) &&
    (Nat.all 8 fun a _ => Nat.all 8 fun a' _ =>
      T.pair[w.b[a]!]![w.b[a']!]! == chainGramN a a') &&
    (Nat.all r fun i _ => !c.testBit i ||
      (let e := w.span[i]!
       decide (e.1 < e.2.1) && decide (e.2.1 ≤ 8) && Nat.all D fun kk _ =>
         Q[i]![kk]! == (if e.2.2 then -1 else 1) * chainSumN Q w.b e.1 e.2.1 kk)) &&
    decide (w.cz < 3 ^ d) &&
    (Nat.all r fun t _ =>
      chainExpN T w.b t % 3 == 0 && chainExpN T w.b t / 3 % 3 == evA T d t w.cz) &&
    Nat.all d fun k _ =>
      let h := w.hyp[k]!
      decide (h.1 < 3) && inOK T d r c h.2 (combN d (3 ^ k) w.cz 1 (3 - h.1))

@[expose] def orthMaskN (T : Tabs) (r k : Nat) : Nat :=
  maskN r fun i => T.pair[k]![i]! == 0 && T.pair[i]![k]! == 0

@[expose] def flagE6N (T : Tabs) (r c : Nat) : Bool :=
  trunc r c == 2 ^ r - 1 || Nat.any r fun k _ => trunc r c == orthMaskN T r k


end CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

end
