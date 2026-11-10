module

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02.SpinNative

set_option compiler.extract_closed false

abbrev Mat (N : Nat) : Type := Vector (Vector Rat N) N

@[expose] def ent {N : Nat} (A : Mat N) (i j : Fin N) : Rat := (A.get i).get j

@[expose] def ofF {N : Nat} (f : Fin N → Fin N → Rat) : Mat N :=
  Vector.ofFn fun i => Vector.ofFn fun j => f i j

@[expose] def oneM (N : Nat) : Mat N := ofF fun i j => if i = j then 1 else 0

@[expose] def zeroM (N : Nat) : Mat N := ofF fun _ _ => 0

@[expose] def addM {N : Nat} (A B : Mat N) : Mat N := ofF fun i j => ent A i j + ent B i j

@[expose] def subM {N : Nat} (A B : Mat N) : Mat N := ofF fun i j => ent A i j - ent B i j

@[expose] def smulM {N : Nat} (c : Rat) (A : Mat N) : Mat N := ofF fun i j => c * ent A i j

@[expose] def mulM {N : Nat} (A B : Mat N) : Mat N :=
  let ks := List.finRange N
  ofF fun i j => ks.foldl (fun acc k =>
    let a := ent A i k
    if a = 0 then acc else acc + a * ent B k j) 0

@[expose] def prodM {N : Nat} : List (Mat N) → Mat N
  | [] => oneM N
  | A :: As => mulM A (prodM As)

@[expose] def entN {a : Nat} (A : Mat a) (i j : Nat) : Rat :=
  if h : i < a then (if h' : j < a then ent A ⟨i, h⟩ ⟨j, h'⟩ else 0) else 0

@[expose] def kronM {a b : Nat} (A : Mat a) (B : Mat b) : Mat (a * b) :=
  ofF fun i j => entN A (i.val / b) (j.val / b) * entN B (i.val % b) (j.val % b)

@[expose] def mI : Mat 2 := oneM 2

@[expose] def mX : Mat 2 := ofF fun i j => if i.val + j.val = 1 then 1 else 0

@[expose] def mZ : Mat 2 := ofF fun i j => if i = j then (if i.val = 0 then 1 else -1) else 0

@[expose] def mJ : Mat 2 := ofF fun i j =>
  if i.val = 0 ∧ j.val = 1 then -1 else if i.val = 1 ∧ j.val = 0 then 1 else 0

@[expose] def str8Tab : List (List Nat) :=
  [[0, 1, 1, 1], [0, 2, 2, 2], [1, 0, 1, 2], [1, 1, 2, 0],
    [1, 2, 0, 1], [2, 0, 2, 1], [2, 1, 0, 2], [2, 2, 1, 0]]

@[expose] def str8 (k i : Nat) : Nat := (str8Tab.getD k []).getD i 0

@[expose] def letter (c : Nat) : Mat 2 := if c = 0 then mI else if c = 1 then mX else mZ

@[expose] def g8 (k : Nat) : Mat 16 :=
  kronM (kronM (kronM (letter (str8 k 0)) (letter (str8 k 1))) (letter (str8 k 2)))
    (letter (str8 k 3))

@[expose] def G8 (_ : Unit := ()) : Mat 16 := prodM (List.ofFn fun k : Fin 8 => g8 k)

@[expose] def gam8 (k : Nat) : Mat 16 := if k < 8 then g8 k else oneM 16

@[expose] def gam9 (k : Nat) : Mat 16 := if k < 8 then g8 k else G8 ()

@[expose] def gam10 (k : Nat) : Mat 32 :=
  if k < 8 then kronM (g8 k) mI
  else if k = 8 then kronM (G8 ()) mX else kronM (G8 ()) mZ

@[expose] def G10 (_ : Unit := ()) : Mat 32 := prodM (List.ofFn fun k : Fin 10 => gam10 k)

@[expose] def gam11 (k : Nat) : Mat 64 :=
  if k < 10 then kronM (gam10 k) mI else kronM (G10 ()) mJ

@[expose] def pairsS8 : List (List (Nat × Nat × Nat × Nat) × List (Nat × Nat × Nat × Nat)) :=
  [([(0, 4, 1, 2), (2, 4, 4, 6)], [(1, 6, 2, 3), (3, 6, 6, 7)]),
    ([(0, 5, 1, 3), (2, 3, 3, 6), (4, 6, 5, 7)], [(2, 3, 3, 7), (4, 6, 5, 7)]),
    ([(0, 4, 1, 5), (2, 3, 4, 6), (5, 7, 6, 7)], [(2, 7, 3, 6), (4, 7, 5, 6)]),
    ([(0, 1, 2, 3)], [(0, 2, 1, 3)])]


@[expose] def pairsS10 : List (List (Nat × Nat × Nat × Nat) × List (Nat × Nat × Nat × Nat)) :=
  [([(0, 9, 1, 8), (2, 6, 3, 8), (4, 8, 5, 7), (6, 9, 7, 8)], [(0, 1, 1, 4), (2, 7, 4, 8), (6, 7, 7, 8)]),
    ([(0, 2, 1, 2), (2, 6, 3, 8), (4, 7, 5, 9), (6, 7, 7, 8)], [(0, 5, 1, 5), (2, 8, 3, 7), (4, 8, 5, 7)]),
    ([(0, 5, 1, 9), (2, 9, 4, 9), (5, 7, 8, 9)], [(0, 4, 1, 3), (3, 6, 4, 7), (5, 6, 6, 9), (7, 8, 8, 9)]),
    ([(0, 6, 1, 9), (2, 4, 3, 8), (4, 8, 5, 7), (7, 9, 8, 9)], [(0, 2, 1, 4), (2, 8, 4, 6), (5, 8, 6, 7), (7, 8, 8, 9)]),
    ([(0, 1, 2, 3)], [(0, 2, 1, 3)])]

@[expose] def treeS10 : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 8), (4, 0), (4, 1), (4, 4), (4, 6), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 8), (7, 0), (7, 2), (7, 3), (7, 5), (7, 6), (7, 7), (8, 1), (8, 6), (8, 7), (8, 8), (9, 0), (9, 5), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 6), (10, 7), (10, 8), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 7), (11, 8), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 8), (13, 0), (13, 1), (13, 4), (13, 6), (14, 7), (14, 8), (15, 2), (15, 3), (15, 5), (15, 6), (15, 7), (16, 1), (16, 6), (16, 7), (16, 8), (17, 0), (17, 5), (18, 0), (18, 1), (18, 2), (18, 3), (18, 4), (18, 6), (19, 0), (19, 2), (19, 3), (19, 5), (20, 0), (20, 1), (20, 2), (20, 3), (20, 4), (20, 5), (20, 8), (21, 0), (21, 4), (21, 6), (22, 7), (22, 8), (23, 2), (23, 3), (23, 5), (23, 8), (24, 1), (24, 7), (24, 8), (25, 0), (26, 0), (26, 3), (26, 4), (26, 7), (26, 8), (27, 1), (27, 3), (27, 4), (27, 7), (27, 8), (28, 0), (28, 1), (28, 5), (30, 5), (30, 8), (31, 1), (31, 2), (31, 5), (31, 8), (32, 0), (32, 5), (33, 0), (33, 1), (33, 4), (34, 0), (34, 1), (34, 2), (34, 4), (35, 6), (36, 0), (36, 6), (36, 7), (37, 2), (37, 3), (37, 5), (37, 6), (37, 8), (38, 2), (38, 3), (38, 5), (38, 7), (39, 1), (39, 6), (40, 0), (40, 5), (42, 0), (42, 2), (42, 3), (44, 5), (44, 6), (45, 0), (45, 2), (47, 2), (47, 3), (48, 2), (49, 1), (51, 0), (53, 2), (54, 2), (54, 3), (55, 1), (57, 3), (58, 3), (59, 0), (59, 1), (59, 6), (60, 0), (60, 1), (60, 3), (60, 5), (60, 8), (61, 2), (62, 6), (64, 3), (64, 5), (64, 6), (64, 7), (65, 1), (65, 7), (67, 0), (67, 1), (67, 6), (68, 0), (68, 2), (68, 5), (69, 0), (69, 1), (69, 2), (69, 8), (72, 3), (72, 5), (73, 7), (75, 1), (75, 3), (75, 8), (76, 0), (76, 5), (79, 8), (80, 0), (80, 5), (81, 1), (81, 4), (82, 2), (83, 6), (84, 7), (85, 1), (87, 2), (90, 0), (92, 2), (93, 2), (93, 3), (96, 3), (97, 3), (101, 1), (103, 2), (104, 0), (105, 2), (105, 5), (109, 4), (112, 8), (115, 0), (117, 7), (119, 0), (129, 4), (134, 4), (142, 0), (149, 4), (150, 4)]


abbrev Q4 : Type := Nat × Nat × Nat × Nat

abbrev Wd : Type := List Q4

@[expose] def Mdd {N : Nat} (Γ : Nat → Mat N) (q : Q4) : Mat N :=
  if q.1 = q.2.1 ∨ q.2.2.1 = q.2.2.2 then oneM N
  else smulM (1 / 2 : Rat) (mulM (subM (Γ q.1) (Γ q.2.1)) (subM (Γ q.2.2.1) (Γ q.2.2.2)))

@[expose] def Mw {N : Nat} (Γ : Nat → Mat N) (w : Wd) : Mat N := prodM (w.map (Mdd Γ))

@[expose] def invW (w : Wd) : Wd := (w.reverse).map fun q => (q.2.2.1, q.2.2.2, q.1, q.2.1)

@[expose] def Mcomm {N : Nat} (Γ : Nat → Mat N) (p : Wd × Wd) : Mat N :=
  mulM (mulM (mulM (Mw Γ p.1) (Mw Γ p.2)) (Mw Γ (invW p.1))) (Mw Γ (invW p.2))

@[expose] def gensM {N : Nat} (Γ : Nat → Mat N) (ps : List (Wd × Wd)) : List (Mat N) :=
  ps.map (Mcomm Γ) ++ ps.map fun p => Mcomm Γ (p.2, p.1)

@[expose] def treeAux {N : Nat} (gs : List (Mat N)) : List (Mat N) → List (Nat × Nat) → List (Mat N)
  | acc, [] => acc
  | acc, (p, g) :: tr => treeAux gs (acc ++ [mulM (gs.getD g (oneM N)) (acc.getD p (oneM N))]) tr

@[expose] def treeTab {N : Nat} (gs : List (Mat N)) (tr : List (Nat × Nat)) : List (Mat N) :=
  treeAux gs [oneM N] tr


@[expose] def closedB {N : Nat} (T gs : List (Mat N)) : Bool :=
  decide T.Nodup && T.all fun x => gs.all fun g => decide (mulM g x ∈ T)

@[expose] def wordsOK (n : Nat) (ps : List (List (Nat × Nat × Nat × Nat) × List (Nat × Nat × Nat × Nat))) : Bool :=
  ps.all fun p => (p.1 ++ p.2).all fun q =>
    decide (q.1 < n ∧ q.2.1 < n ∧ q.2.2.1 < n ∧ q.2.2.2 < n ∧ q.1 ≠ q.2.1 ∧ q.2.2.1 ≠ q.2.2.2)


end CFSG.ComponentClassification.Sol76.Sig.GSYard02.SpinNative

end
