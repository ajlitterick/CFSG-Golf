module

public section

namespace Certificates.DepASmall

set_option compiler.extract_closed false

@[expose] def ggDepANDot (p : Nat) (a b : List Nat) : Nat :=
  (List.zipWith (fun x y => x * y) a b).sum % p

@[expose] def ggDepANSub (p : Nat) (a b : List Nat) : List Nat :=
  List.zipWith (fun x y => (x + (p - y % p)) % p) a b

@[expose] def ggDepANSmul (p k : Nat) (a : List Nat) : List Nat := a.map fun x => (k * x) % p

@[expose] def ggDepANH (p N i : Nat) : List Nat := (List.range N).map fun j =>
  if j + 1 = N then 0
  else ((if j = i then 1 else 0) + (if i + 2 = N then 1 else 0) +
    (p - (if j = i + 1 then 1 else 0))) % p

@[expose] def ggDepANA (p N i : Nat) : List Nat := (List.range N).map fun j =>
  if j + 1 = N then 0 else ((if j = i then 1 else 0) + (p - (if j = i + 1 then 1 else 0))) % p

@[expose] def ggDepANX (N : Nat) : List Nat :=
  (List.range N).map fun j => if j + 1 = N then 1 else 0

abbrev GGDepANPair := List Nat × List Nat

@[expose] def ggDepANConj (p : Nat) (q g : GGDepANPair) : GGDepANPair :=
  (ggDepANSub p q.1 (ggDepANSmul p (ggDepANDot p g.2 q.1) g.1),
    ggDepANSub p q.2 (ggDepANSmul p (ggDepANDot p q.2 g.1) g.2))

@[expose] def ggDepANGen (p N : Nat) (ha aa : List Nat) (i : Nat) : GGDepANPair :=
  if i + 1 < N then (ggDepANH p N i, ggDepANA p N i) else (ha, aa)

@[expose] def ggDepANWord (p N : Nat) (q : GGDepANPair) (w : List Nat) (ha aa : List Nat) :
    GGDepANPair :=
  w.foldr (fun g acc => ggDepANConj p acc (ggDepANGen p N ha aa g)) q

@[expose] def ggDepANFirstNZ (p : Nat) (l : List Nat) : Option Nat :=
  (List.range l.length).find? fun j => l.getD j 0 % p != 0

@[expose] def ggDepANPar (p : Nat) (a b : List Nat) : Bool :=
  match ggDepANFirstNZ p a with
  | none => false
  | some i => b.getD i 0 % p != 0 &&
      (List.range a.length).all fun k =>
        (a.getD i 0 * b.getD k 0) % p == (b.getD i 0 * a.getD k 0) % p

@[expose] def ggDepANEqScaled (p k₁ : Nat) (u : List Nat) (k₂ : Nat) (v : List Nat) : Bool :=
  (List.zipWith (fun x y => (k₁ * x) % p == (k₂ * y) % p) u v).all id

@[expose] def ggDepANTestPair (p : Nat) (q1 q2 : GGDepANPair) : Bool :=
  (match ggDepANFirstNZ p q1.1 with
    | none => false
    | some i => ggDepANPar p q1.1 q2.1 &&
        !ggDepANEqScaled p (q1.1.getD i 0) q1.2 (q2.1.getD i 0) q2.2) ||
  (match ggDepANFirstNZ p q1.2 with
    | none => false
    | some j => ggDepANPar p q1.2 q2.2 &&
        !ggDepANEqScaled p (q1.2.getD j 0) q1.1 (q2.2.getD j 0) q2.1)

structure GGDepANWit where
  g1 : Nat
  w1 : List Nat
  g2 : Nat
  w2 : List Nat

@[expose] def ggDepANWitTest (p N : Nat) (w : GGDepANWit) (ha aa : List Nat) : Bool :=
  ggDepANTestPair p (ggDepANWord p N (ggDepANGen p N ha aa w.g1) w.w1 ha aa)
    (ggDepANWord p N (ggDepANGen p N ha aa w.g2) w.w2 ha aa)

@[expose] def ggDepANWitValid (N : Nat) (w : GGDepANWit) : Bool :=
  decide (w.g1 < N) && decide (w.g2 < N) && w.w1.all (fun g => decide (g < N)) &&
    w.w2.all fun g => decide (g < N)

@[expose] def ggDepANHaParam (p N b c0 n s t : Nat) : List Nat := (List.range N).map fun j =>
  if j + 1 = N then t % p
  else if b = 0 then (if j = 0 then s % p else if j ≤ c0 then n % p else 0)
  else (s + (if j ≤ c0 then n else 0)) % p

@[expose] def ggDepANAaParam (p N b c0 m u v : Nat) : List Nat := (List.range N).map fun j =>
  if j + 1 = N then v % p
  else if b = 0 then
    (if j = 0 then (if c0 + 2 = N then (m + u) % p else (u + (p - (m * c0) % p)) % p)
      else if c0 + 2 = N then u % p else if j ≤ c0 then (u + m) % p else u % p)
  else (u + (if j ≤ c0 then m else 0)) % p

abbrev GGDepANData := List ((Nat × Nat × Nat × Nat) × List GGDepANWit)

@[expose] def ggDepANPatB (N b c0 mi ni : Nat) : Bool :=
  decide (b < N - 1) && decide (c0 < N - 1) && (decide (b = 0) || decide (b + 2 = N)) &&
    decide (c0 ≠ b) &&
    (((decide ((if b = 0 then c0 - 1 else c0) = 0) ||
          decide ((if b = 0 then c0 - 1 else c0) + 1 = N - 2)) &&
        ((mi == 1 && ni == 1) || (mi == 1 && ni == 2) || (mi == 2 && ni == 1))) ||
      (decide (3 ≤ N - 2) &&
        (decide ((if b = 0 then c0 - 1 else c0) = 1) ||
          decide ((if b = 0 then c0 - 1 else c0) + 2 = N - 2)) && mi == 1 && ni == 1) ||
      (decide (N - 2 = 5) && decide ((if b = 0 then c0 - 1 else c0) = 2) && mi == 1 && ni == 1))


end Certificates.DepASmall
