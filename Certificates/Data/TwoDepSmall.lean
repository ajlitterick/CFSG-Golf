module

public import Certificates.Data.DepASmall

public section

namespace Certificates.TwoDepSmall

open Certificates.DepASmall

set_option compiler.extract_closed false

@[expose] def ggTWNX (N : Nat) : List Nat :=
  (List.range (N - 1)).map fun j => if j + 2 = N then 1 else 0

@[expose] def ggTWNH (p N i : Nat) : List Nat := (List.range (N - 1)).map fun j =>
  if j + 2 = N then 0
  else if i = 0 then (p - (j + 2) % p) % p
  else if j + 1 = i then 1 else 0

@[expose] def ggTWNA (p N i : Nat) : List Nat := (List.range (N - 1)).map fun j =>
  if j + 2 = N then 0
  else if j + 1 = i then 2 % p
  else if j + 2 = i || j = i then (p - 1) % p else 0

@[expose] def ggTWNZ (p N pos : Nat) : List Nat := (List.range (N - 1)).map fun j =>
  if pos = 0 then (if j + 2 = N then 0 else (j + 1) % p) else (if j + 3 = N then 1 else 0)

@[expose] def ggTWNInJ (N pos c : Nat) : Bool :=
  if pos = 0 then decide (1 ≤ c) && decide (c + 3 ≤ N) else decide (c + 4 ≤ N)

@[expose] def ggTWNPlace (pos c : Nat) : Nat := if pos = 0 then c - 1 else c

@[expose] def ggTWNAdd (p : Nat) (a b : List Nat) : List Nat :=
  List.zipWith (fun x y => (x + y) % p) a b

@[expose] def ggTWNRefl (p : Nat) (g : GGDepANPair) (v : List Nat) : List Nat :=
  ggDepANSub p v (ggDepANSmul p (ggDepANDot p g.2 v) g.1)

@[expose] def ggTWNGen (p N : Nat) (news : List GGDepANPair) (g : Nat) : GGDepANPair :=
  if g + 1 < N then (ggTWNH p N g, ggTWNA p N g) else news.getD (g + 1 - N) ([], [])

@[expose] def ggTWNWord (p N : Nat) (news : List GGDepANPair) (q : GGDepANPair) (w : List Nat) :
    GGDepANPair :=
  w.foldr (fun g acc => ggDepANConj p acc (ggTWNGen p N news g)) q

@[expose] def ggTWNApply (p N : Nat) (w : List Nat) (v : List Nat) : List Nat :=
  w.foldr (fun g acc => ggTWNRefl p (ggTWNH p N g, ggTWNA p N g) acc) v

structure GGTWNLine where
  g : Nat
  w : List Nat
  i : Nat
  wv : List Nat

inductive GGTWNKill
  | tv (w : GGDepANWit)
  | line (w : GGTWNLine)

@[expose] def ggTWNRoots (p N : Nat) : List (List Nat) :=
  (List.range (N - 1)).flatMap fun i => (List.range (N - 1)).flatMap fun j =>
    if i ≤ j then
      let v := ((List.range (N - 1)).filter fun k => decide (i ≤ k) && decide (k ≤ j)).foldl
        (fun acc k => ggTWNAdd p acc (ggTWNH p N k)) (List.replicate (N - 1) 0)
      [v, ggDepANSmul p (p - 1) v]
    else []

@[expose] def ggTWNRootsOK (p N : Nat) (R : List (List Nat)) : Bool :=
  (List.range (N - 1)).all (fun i => R.contains (ggTWNH p N i)) &&
  R.all (fun u => (ggDepANFirstNZ p (u.take (N - 2))).isSome) &&
  R.all fun u => (List.range (N - 1)).all fun g =>
    R.contains (ggTWNRefl p (ggTWNH p N g, ggTWNA p N g) u)

@[expose] def ggTWNKillValid (N G : Nat) : GGTWNKill → Bool
  | .tv w => decide (w.g1 < G) && decide (w.g2 < G) && w.w1.all (fun g => decide (g < G)) &&
      w.w2.all fun g => decide (g < G)
  | .line w => decide (w.g < G) && w.w.all (fun g => decide (g < G)) && decide (w.i + 1 < N) &&
      w.wv.all fun g => decide (g + 1 < N)

@[expose] def ggTWNKillTest (p N : Nat) (news : List GGDepANPair) (R : List (List Nat)) :
    GGTWNKill → Bool
  | .tv w => ggDepANTestPair p (ggTWNWord p N news (ggTWNGen p N news w.g1) w.w1)
      (ggTWNWord p N news (ggTWNGen p N news w.g2) w.w2)
  | .line w =>
    let s := ggTWNWord p N news (ggTWNGen p N news w.g) w.w
    let sv := ggTWNRefl p s (ggTWNApply p N w.wv (ggTWNH p N w.i))
    ggDepANDot p s.2 (ggTWNX N) == 0 &&
      R.all fun u => !ggDepANPar p (u.take (N - 2)) (sv.take (N - 2))

@[expose] def ggTWNDecode (p : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => (k % p) :: ggTWNDecode p n (k / p)

@[expose] def ggTWNSolH (p N pos : Nat) (tgt : Nat → Nat) : List (List Nat) :=
  let As := (List.range (N - 1)).map fun c => ggTWNA p N c
  (List.range (p ^ (N - 1))).filterMap fun k =>
    let v := ggTWNDecode p (N - 1) k
    if (List.range (N - 1)).all (fun c =>
        !ggTWNInJ N pos c || ggDepANDot p (As.getD c []) v == tgt c % p) then some v else none

@[expose] def ggTWNSolA (p N pos : Nat) (tgt : Nat → Nat) : List (List Nat) :=
  let Hs := (List.range (N - 1)).map fun c => ggTWNH p N c
  (List.range (p ^ (N - 1))).filterMap fun k =>
    let v := ggTWNDecode p (N - 1) k
    if (List.range (N - 1)).all (fun c =>
        !ggTWNInJ N pos c || ggDepANDot p v (Hs.getD c []) == tgt c % p) then some v else none

@[expose] def ggTWNPat1B (N pos c0 mi ni : Nat) : Bool :=
  ggTWNInJ N pos c0 &&
    ((((ggTWNPlace pos c0 == 0) || decide (ggTWNPlace pos c0 + 1 = N - 3)) &&
        ((mi == 1 && ni == 1) || (mi == 1 && ni == 2) || (mi == 2 && ni == 1))) ||
      (decide (3 ≤ N - 3) &&
        ((ggTWNPlace pos c0 == 1) || decide (ggTWNPlace pos c0 + 2 = N - 3)) &&
        mi == 1 && ni == 1) ||
      (decide (5 ≤ N - 3) && decide (N - 3 ≤ 7) &&
        ((ggTWNPlace pos c0 == 2) || decide (ggTWNPlace pos c0 + 3 = N - 3)) &&
        mi == 1 && ni == 1))

@[expose] def ggTWNPat2B (N pos c : Nat) (c2 : Option Nat) : Bool :=
  ggTWNInJ N pos c &&
    ((ggTWNPlace pos c == 0) || decide (ggTWNPlace pos c + 1 = N - 3)) &&
    (match c2 with
      | none => true
      | some c' => ggTWNInJ N pos c' &&
          ((ggTWNPlace pos c == 0 && decide (ggTWNPlace pos c' + 1 = N - 3)) ||
            (decide (ggTWNPlace pos c + 1 = N - 3) && ggTWNPlace pos c' == 0)))


@[expose] def ggTWNTgt2 (p : Nat) (c2 : Option Nat) (c : Nat) : Nat :=
  match c2 with
  | none => 0
  | some c' => if c = c' then (p - 1) % p else 0


@[expose] def ggTWNCode : Option Nat → Nat
  | none => 0
  | some c' => c' + 1


end Certificates.TwoDepSmall
