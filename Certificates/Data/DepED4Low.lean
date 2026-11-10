module

public import Certificates.Data.TwoDepSmallLow

public section

namespace Certificates.DepED4Low

open Certificates.DepASmall Certificates.TwoDepSmall Certificates.TwoDepSmallLow

set_option compiler.extract_closed false

@[expose] def ggDepELNX : List Nat := [0, 0, 0, 0, 0, 1]

@[expose] def ggDepELNH (i : Nat) : List Nat :=
  [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 1, 0], [1, 0, 2, 0, 1, 0]].getD i []

@[expose] def ggDepELNA (i : Nat) : List Nat :=
  [[2, 0, 2, 0, 0, 0], [0, 2, 0, 2, 0, 0], [2, 0, 2, 2, 0, 0], [0, 2, 2, 2, 2, 0],
    [0, 0, 0, 2, 2, 0], [0, 0, 0, 0, 2, 0]].getD i []

@[expose] def ggDepELNZ : List Nat := [2, 1, 2, 2, 1, 0]

@[expose] def ggDepELNJ : List Nat := [1, 2, 3, 4]

@[expose] def ggDepELNLeaves : List Nat := [1, 2, 4]

@[expose] def ggDepELNInJ (c : Nat) : Bool := decide (1 ≤ c) && decide (c ≤ 4)

@[expose] def ggDepELNGen (news : List GGDepANPair) (g : Nat) : GGDepANPair :=
  if g < 6 then (ggDepELNH g, ggDepELNA g) else news.getD (g - 6) ([], [])

@[expose] def ggDepELNWord (news : List GGDepANPair) (q : GGDepANPair) (w : List Nat) :
    GGDepANPair :=
  w.foldr (fun g acc => ggDepANConj 3 acc (ggDepELNGen news g)) q

@[expose] def ggDepELTvValid (G : Nat) (w : GGDepANWit) : Bool :=
  decide (w.g1 < G) && decide (w.g2 < G) && w.w1.all (fun g => decide (g < G)) &&
    w.w2.all fun g => decide (g < G)

@[expose] def ggDepELTvTest (news : List GGDepANPair) (w : GGDepANWit) : Bool :=
  ggDepANTestPair 3 (ggDepELNWord news (ggDepELNGen news w.g1) w.w1)
    (ggDepELNWord news (ggDepELNGen news w.g2) w.w2)

@[expose] def ggDepELSolH (tgt : Nat → Nat) : List (List Nat) :=
  (List.range (3 ^ 6)).filterMap fun k =>
    let v := ggTWNDecode 3 6 k
    if ggDepELNJ.all (fun c => ggDepANDot 3 (ggDepELNA c) v == tgt c % 3) then some v else none

@[expose] def ggDepELSolA (tgt : Nat → Nat) : List (List Nat) :=
  (List.range (3 ^ 6)).filterMap fun k =>
    let v := ggTWNDecode 3 6 k
    if ggDepELNJ.all (fun c => ggDepANDot 3 v (ggDepELNH c) == tgt c % 3) then some v else none

@[expose] def ggDepELY0One (a : List Nat) : List Nat :=
  ggDepANSub 3 ggDepELNZ
    (ggDepANSmul 3 ((ggDepANDot 3 a ggDepELNZ * ggTWLInv 3 (ggDepANDot 3 a ggDepELNX)) % 3)
      ggDepELNX)

@[expose] def ggDepELY0 (news : List GGDepANPair) : List Nat :=
  match news.find? (fun q => ggDepANDot 3 q.2 ggDepELNX % 3 != 0) with
  | some q => ggDepELY0One q.2
  | none => List.replicate 6 0

@[expose] def ggDepELNOGens (news : List GGDepANPair) : List GGDepANPair :=
  ggDepELNJ.map (fun c => (ggDepELNH c, ggDepELNA c)) ++ news


end Certificates.DepED4Low

end
