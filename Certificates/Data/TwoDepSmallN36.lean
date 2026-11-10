module

public import Certificates.Data.TwoDepSmallN

public section

namespace Certificates.TwoDepSmallN

open Certificates.DepASmall Certificates.TwoDepSmall

set_option compiler.extract_closed false

@[expose] def ggTWDRefVec (p : Nat) (q : GGDepANPair) (v : List Nat) : List Nat :=
  ggDepANSub p v (ggDepANSmul p (ggDepANDot p q.2 v) q.1)

@[expose] def ggTWDWordVec (p : Nat) (qs : List GGDepANPair) (w : List Nat) (v : List Nat) :
    List Nat :=
  w.foldr (fun g acc => ggTWDRefVec p (qs.getD g ([], [])) acc) v

@[expose] def ggTWDBasis (N k : Nat) : List Nat :=
  (List.range N).map fun j => if j = k then 1 else 0

@[expose] def ggTWDE6M (i j : Nat) : Nat :=
  if i = j then 1
  else if (i, j) ∈ [(0, 2), (2, 0), (1, 3), (3, 1), (2, 3), (3, 2), (3, 4), (4, 3), (4, 5), (5, 4)]
    then 3 else 2

@[expose] def ggTWDPowVec (p : Nat) (qi qj : GGDepANPair) (m : Nat) (v : List Nat) : List Nat :=
  (List.range m).foldl (fun acc _ => ggTWDRefVec p qi (ggTWDRefVec p qj acc)) v

structure GGTWDOut where
  sw : List (Nat × List Nat)
  gw : List (Nat × List Nat)
  ot : List (Nat × Nat)

@[expose] def ggTWDGenList (p N : Nat) (news : List GGDepANPair) : List GGDepANPair :=
  (List.range (N - 1)).map (fun g => (ggDepANH p N g, ggDepANA p N g)) ++ news

@[expose] def ggTWDOutS (p N : Nat) (news : List GGDepANPair) (O : GGTWDOut) : List GGDepANPair :=
  O.sw.map fun e => ggTWDWord p N news (ggTWDGen p N news e.1) e.2

@[expose] def ggTWDOrbit (p N : Nat) (news : List GGDepANPair) (ot : List (Nat × Nat)) :
    List (List Nat) :=
  ot.foldl (fun acc e =>
    acc ++ [ggTWDRefVec p ((ggTWDGenList p N news).getD e.2 ([], [])) (acc.getD e.1 [])])
    [ggDepANX N]

@[expose] def ggTWDOutValid (G : Nat) (O : GGTWDOut) : Bool :=
  decide (O.sw.length = 6) &&
    O.sw.all (fun e => decide (e.1 < G) && e.2.all fun g => decide (g < G)) &&
    decide (O.gw.length = G) &&
    O.gw.all (fun e => decide (e.1 < 6) && e.2.all fun i => decide (i < 6)) &&
    decide (O.ot.length = 71) &&
    (List.range O.ot.length).all fun t =>
      decide ((O.ot.getD t (0, 0)).1 ≤ t) && decide ((O.ot.getD t (0, 0)).2 < G)

@[expose] def ggTWDOutOK (p N : Nat) (news : List GGDepANPair) (O : GGTWDOut) : Bool :=
  let gs := ggTWDGenList p N news
  let ss := ggTWDOutS p N news O
  ggTWDOutValid gs.length O &&
    (List.range 6).all (fun i => (List.range 6).all fun j => (List.range N).all fun k =>
      ggTWDPowVec p (ss.getD i ([], [])) (ss.getD j ([], [])) (ggTWDE6M i j) (ggTWDBasis N k) ==
        ggTWDBasis N k) &&
    (List.range gs.length).all (fun g =>
      let e := O.gw.getD g (0, [])
      (List.range N).all fun k =>
        ggTWDRefVec p (gs.getD g ([], [])) (ggTWDBasis N k) ==
          ggTWDWordVec p ss (e.2 ++ e.1 :: e.2.reverse) (ggTWDBasis N k)) &&
    let vs := ggTWDOrbit p N news O.ot
    decide (vs.length = 72) && decide vs.Nodup


end Certificates.TwoDepSmallN

end
