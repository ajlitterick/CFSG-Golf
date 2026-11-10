module

public import Certificates.Data.TwoDepSmall

public section

namespace Certificates.TwoDepSmallLow

open Certificates.DepASmall Certificates.TwoDepSmall

set_option compiler.extract_closed false

@[expose] def ggTWLVecEq (p : Nat) (u v : List Nat) : Bool :=
  decide (u.length = v.length) && (List.zipWith (fun a b => a % p == b % p) u v).all id

@[expose] def ggTWLBasis (d k : Nat) : List Nat :=
  (List.range d).map fun j => if j = k then 1 else 0

@[expose] def ggTWLMatOfPair (p d : Nat) (q : GGDepANPair) : List (List Nat) :=
  (List.range d).map fun k => ggTWNRefl p q (ggTWLBasis d k)

@[expose] def ggTWLMatApply (p d : Nat) (A : List (List Nat)) (v : List Nat) : List Nat :=
  (List.zip v A).foldl (fun acc t => ggTWNAdd p acc (ggDepANSmul p t.1 t.2)) (List.replicate d 0)

@[expose] def ggTWLMatMul (p d : Nat) (A B : List (List Nat)) : List (List Nat) :=
  B.map fun col => ggTWLMatApply p d A col

@[expose] def ggTWLMatOne (d : Nat) : List (List Nat) := (List.range d).map (ggTWLBasis d)

@[expose] def ggTWLMatEq (p : Nat) (A B : List (List Nat)) : Bool :=
  decide (A.length = B.length) && (List.zipWith (ggTWLVecEq p) A B).all id

@[expose] def ggTWLReplay (p d : Nat) (T : List (List (List Nat))) (par : List (Nat × Nat)) :
    List (List (List Nat)) :=
  par.foldl (fun L e => L ++ [ggTWLMatMul p d (L.getD e.1 []) (T.getD e.2 [])]) [ggTWLMatOne d]

@[expose] def ggTWLNodup (p : Nat) : List (List (List Nat)) → Bool
  | [] => true
  | a :: l => l.all (fun b => !ggTWLMatEq p a b) && ggTWLNodup p l

@[expose] def ggTWLEnumOK (p d : Nat) (T : List (List (List Nat))) (par : List (Nat × Nat)) :
    Bool :=
  let L := ggTWLReplay p d T par
  (List.range par.length).all (fun i => decide ((par.getD i (0, 0)).1 < i + 1) &&
      decide ((par.getD i (0, 0)).2 < T.length)) &&
    L.all (fun a => T.all fun t => L.any fun b => ggTWLMatEq p b (ggTWLMatMul p d a t)) &&
    ggTWLNodup p L


@[expose] def ggTWLInv (p a : Nat) : Nat :=
  ((List.range p).find? fun k => decide (0 < k) && (k * a) % p == 1).getD 0

@[expose] def ggTWLY0One (p N pos : Nat) (a : List Nat) : List Nat :=
  ggDepANSub p (ggTWNZ p N pos)
    (ggDepANSmul p ((ggDepANDot p a (ggTWNZ p N pos) * ggTWLInv p (ggDepANDot p a (ggTWNX N))) % p)
      (ggTWNX N))

@[expose] def ggTWLY0 (p N pos : Nat) (news : List GGDepANPair) : List Nat :=
  match news.find? (fun q => ggDepANDot p q.2 (ggTWNX N) % p != 0) with
  | some q => ggTWLY0One p N pos q.2
  | none => List.replicate (N - 1) 0

@[expose] def ggTWLOGens (p N pos : Nat) (news : List GGDepANPair) : List GGDepANPair :=
  ((List.range (N - 1)).filter (fun c => ggTWNInJ N pos c)).map
    (fun c => (ggTWNH p N c, ggTWNA p N c)) ++ news


@[expose] def ggTWLStable (p : Nat) (og : List GGDepANPair) (cs R : List (List Nat)) : Bool :=
  cs.all (fun c => R.any (ggTWLVecEq p c)) &&
    R.all fun u => og.all fun g => R.any (ggTWLVecEq p (ggTWNRefl p g u))

@[expose] def ggTWLParMod (p : Nat) (y u v : List Nat) : Bool :=
  (List.range p).any fun c => decide (c ≠ 0) && (List.range p).any fun d =>
    ggTWLVecEq p v (ggTWNAdd p (ggDepANSmul p c u) (ggDepANSmul p d y))

structure GGTWLHK where
  g : Nat
  w : List Nat
  oc : Nat
  ow : List Nat


@[expose] def ggTWLWordMat (p d : Nat) (Ts : List (List (List Nat))) (w : List Nat) :
    List (List Nat) :=
  w.foldr (fun k acc => ggTWLMatMul p d (Ts.getD k []) acc) (ggTWLMatOne d)

@[expose] def ggTWLMatPow (p d : Nat) (A : List (List Nat)) : Nat → List (List Nat)
  | 0 => ggTWLMatOne d
  | k + 1 => ggTWLMatMul p d A (ggTWLMatPow p d A k)

@[expose] def ggTWLFact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * ggTWLFact n

@[expose] def ggTWLWeylTypes (r : Nat) : List (Nat × Nat) :=
  (if 1 ≤ r then [(ggTWLFact (r + 1), if r = 1 then 2 else 1)] else []) ++
  (if 2 ≤ r then [(2 ^ r * ggTWLFact r, 2)] else []) ++
  (if 4 ≤ r then [(2 ^ (r - 1) * ggTWLFact r, if r % 2 = 0 then 2 else 1)] else []) ++
  (if r = 6 then [(51840, 1)] else []) ++ (if r = 7 then [(2903040, 2)] else []) ++
  (if r = 8 then [(696729600, 2)] else []) ++ (if r = 4 then [(1152, 2)] else []) ++
  (if r = 2 then [(12, 2)] else [])

@[expose] def ggTWLPZArith (N K : Nat) (hasCen : Bool) : Bool :=
  decide (0 < K) && (List.range 3).all fun i => (ggTWLWeylTypes (N - 3 + i)).all fun t =>
    t.1 % K != 0 || (t.1 == K && t.2 == 1 && hasCen)

structure GGTWLPZ where
  c0 : Nat
  fixs : List (Nat × List Nat)
  orbs : List (Nat × List Nat × List Nat)
  hg : List Nat


@[expose] def ggTWLCartanE (p i j : Nat) : Nat :=
  if i = j then 2 % p
  else if (i = 0 && j = 2) || (j = 0 && i = 2) || (i = 1 && j = 3) || (j = 1 && i = 3) ||
      (2 ≤ i && i + 1 = j) || (2 ≤ j && j + 1 = i) then (p - 1) % p else 0

@[expose] def ggTWLE6M (i j : Nat) : Nat :=
  if i = j then 1
  else if (i, j) ∈ [(0, 2), (2, 0), (1, 3), (3, 1), (2, 3), (3, 2), (3, 4), (4, 3), (4, 5), (5, 4)]
    then 3 else 2


@[expose] def ggTWLOrbitPts (p N : Nat) (news : List GGDepANPair) (ot : List (Nat × Nat)) :
    List (List Nat) :=
  ot.foldl (fun L e =>
    L ++ [ggTWNRefl p (ggTWNGen p N news e.2) (L.getD e.1 [])]) [ggTWNX N]


end Certificates.TwoDepSmallLow

end
