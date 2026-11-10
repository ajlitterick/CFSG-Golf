module

public section

namespace MonsterB.P0Rank

set_option compiler.extract_closed false

@[expose] def colsAct : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, x => (if x % 2 = 1 then c else 0) ^^^ colsAct cs (x / 2)

@[expose] def colsOf (n : Nat) (f : Nat → Nat) : List Nat :=
  (List.range n).map fun b => f (2 ^ b)

@[expose] def actK (cols : List (List Nat)) (κ x : Nat) : Nat :=
  (List.range cols.length).foldr
    (fun k y => if κ.testBit k then colsAct (cols.getD k []) y else y) x


@[expose] def maskT : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, k => (if c.testBit k then 1 else 0) + 2 * maskT cs k


structure Data where
  beta : List (List Nat)
  uConjL : List (List (Nat × Nat))
  uConjT : List (List Nat)
  uSq : List (Nat × Nat)
  uComm : List (List (Nat × Nat))

@[expose] def Data.aCols (dat : Data) : List (List Nat) := dat.uConjL.map (·.map (·.1))

@[expose] def qN (beta : List (List Nat)) (σ : Nat) : Nat :=
  (List.range 16).foldl
    (fun acc j => if σ.testBit j then acc ^^^ colsAct ((beta.getD j []).take j) σ else acc) 0

@[expose] def betaN (beta : List (List Nat)) (σ δ : Nat) : Nat :=
  colsAct ((List.range 16).map fun i => colsAct (beta.getD i []) δ) σ

@[expose] def swalk {α : Type} (cands : α → List Nat) (upd : α → Nat → α)
    (visit : List Nat → α → Bool) : Nat → List Nat → Nat → α → Bool
  | 0, _, _, _ => false
  | fuel + 1, node, top, a =>
    visit node a && (cands a).all fun v =>
      if 2 ^ top ≤ v && node.all (fun x => v ≤ v ^^^ x) then
        swalk cands upd visit fuel (node ++ node.map (v ^^^ ·)) (Nat.log2 v + 1) (upd a v)
      else true


@[expose] def embCols : List Nat := [8, 32, 64, 128, 256]

@[expose] def emb (z : Nat) : Nat := colsAct embCols z


inductive Fact where
  | sq (κ s t : Nat)
  | comm (κ κ' s t : Nat)
  | conj (κ δ c : Nat)
  deriving DecidableEq, Inhabited

@[expose] def findSq (F : List Fact) (κ : Nat) : Option Nat :=
  F.findSome? fun
    | .sq a s _ => if a = κ then some s else none
    | _ => none

@[expose] def findComm (F : List Fact) (κ κ' : Nat) : Option Nat :=
  F.findSome? fun
    | .comm a b s _ => if a = κ ∧ b = κ' then some s else none
    | _ => none

@[expose] def findConj (F : List Fact) (κ δ : Nat) : Option Nat :=
  F.findSome? fun
    | .conj a d c => if a = κ ∧ d = δ then some c else none
    | _ => none

@[expose] def blockRows (w : Nat) (terms : List (Nat × List Nat)) (rhs : Nat) :
    List (List (Nat × Nat) × Bool) :=
  (List.range w).map fun k => (terms.map fun t => (t.1, maskT t.2 k), rhs.testBit k)

@[expose] def c1 (dat : Data) (κ : Nat) : List Nat := colsOf 16 fun x => x ^^^ actK dat.aCols κ x

@[expose] def sysBlocks (dat : Data) (F : List Fact) (ds ks : List Nat) :
    List ((Nat × Nat × Nat) × List (List (Nat × Nat) × Bool)) :=
  let a := ks.length
  let e1 := (List.range a).flatMap fun j =>
    match findSq F (ks.getD j 0) with
    | some s => [((0, j, 0), blockRows 16 [(j, c1 dat (ks.getD j 0))] s)]
    | none => []
  let e2 := (List.range a).flatMap fun j => ((List.range a).filter (j < ·)).flatMap fun k =>
    match findComm F (ks.getD j 0) (ks.getD k 0) with
    | some s => [((1, j, k), blockRows 16 [(j, c1 dat (ks.getD k 0)), (k, c1 dat (ks.getD j 0))] s)]
    | none => []
  let e3 := (List.range ds.length).flatMap fun i => (List.range a).flatMap fun j =>
    match findConj F (ks.getD j 0) (ds.getD i 0) with
    | some c => [((2, i, j), blockRows 9 [(j, colsOf 16 fun x => betaN dat.beta x (ds.getD i 0)),
        (a + i, colsOf 9 fun x => x ^^^ actK dat.uConjT (ks.getD j 0) x)] c)]
    | none => []
  e1 ++ e2 ++ e3

@[expose] def sysRows (dat : Data) (F : List Fact) (ds ks : List Nat) :
    List (List (Nat × Nat) × Bool) :=
  (sysBlocks dat F ds ks).flatMap (·.2)

@[expose] def farkasOK (nv : Nat) (rows : List (List (Nat × Nat) × Bool)) (sel : List Bool) :
    Bool :=
  let ch := (rows.zip sel).filterMap fun p => if p.2 then some p.1 else none
  ch.foldl (fun b r => b ^^ r.2) false &&
    (rows.all fun r => r.1.all fun t => t.1 < nv) &&
    (List.range nv).all fun v =>
      ch.foldl (fun m r => r.1.foldl (fun m t => if t.1 = v then m ^^^ t.2 else m) m) 0 == 0

@[expose] def packRow (r : List (Nat × Nat) × Bool) : Nat :=
  r.1.foldl (fun x t => x ^^^ (t.2 <<< (16 * t.1))) 0

@[expose] def gaussReduce : Nat → List (Nat × Nat × Bool × Nat) → Nat → Bool → Nat →
    List (Nat × Nat × Bool × Nat) ⊕ Nat
  | 0, piv, _, _, _ => .inl piv
  | fuel + 1, piv, x, r, c =>
    if x = 0 then (if r then .inr c else .inl piv)
    else
      let p := Nat.log2 x
      match piv.find? (·.1 = p) with
      | some (_, px, pr, pc) => gaussReduce fuel piv (x ^^^ px) (r ^^ pr) (c ^^^ pc)
      | none => .inl ((p, x, r, c) :: piv)

@[expose] def gaussGo (n fuel : Nat) : List (List (Nat × Nat) × Bool) → Nat →
    List (Nat × Nat × Bool × Nat) → Option (List Bool)
  | [], _, _ => none
  | row :: rest, i, piv =>
    match gaussReduce fuel piv (packRow row) row.2 (2 ^ i) with
    | .inr c => some ((List.range n).map c.testBit)
    | .inl piv' => gaussGo n fuel rest (i + 1) piv'

@[expose] def gaussSel (nv : Nat) (rows : List (List (Nat × Nat) × Bool)) : Option (List Bool) :=
  gaussGo rows.length (16 * nv + 1) rows 0 []

@[expose] def basisOf (l : List Nat) : List Nat :=
  l.foldl (fun bs x =>
    let r := bs.foldl (fun y b => min y (y ^^^ b)) x
    if r = 0 then bs else bs ++ [r]) []

@[expose] def basisIn (l : List Nat) : List Nat :=
  (basisOf (l.mergeSort fun a b => a ≤ b)).filter l.contains

@[expose] def farkasCase (dat : Data) (F : List Fact) (node ks : List Nat) : Bool :=
  let ds := basisIn node
  let kb := basisIn ks
  let nv := kb.length + ds.length
  let rows := sysRows dat F ds kb
  match gaussSel nv rows with
  | some sel => farkasOK nv rows sel
  | none => false

@[expose] def wwalk (dat : Data) (F : List Fact) (node M' : List Nat) (a : Nat) : Bool :=
  swalk (fun c : List Nat => c) (fun c v => let p := 2 ^ (Nat.log2 v + 1); c.filter (p ≤ ·))
    (fun V _ => a * V.length ≤ 2 ^ 14 || farkasCase dat F node V) 11 [0] 0 M'

@[expose] def candOK (dat : Data) (F : List Fact) (node M' : List Nat) (a : Nat) : Bool :=
  (a * M'.length ≤ 2 ^ 15 && farkasCase dat F node M') ||
    (a * M'.length ≤ 2 ^ 16 && wwalk dat F node M' a)


@[expose] def gam (beta : List (List Nat)) (s s' : Nat) : Nat :=
  (List.range 16).foldl (fun acc j =>
    if s'.testBit j then
      (List.range 16).foldl (fun acc i =>
        if j < i && s.testBit i then acc ^^^ (beta.getD i []).getD j 0 else acc) acc
    else acc) 0

@[expose] def lmul (beta : List (List Nat)) (x y : Nat × Nat) : Nat × Nat :=
  (x.1 ^^^ y.1, x.2 ^^^ y.2 ^^^ gam beta x.1 y.1)

@[expose] def linv (beta : List (List Nat)) (x : Nat × Nat) : Nat × Nat :=
  (x.1, x.2 ^^^ gam beta x.1 x.1)

@[expose] def conjk (dat : Data) (k : Nat) (x : Nat × Nat) : Nat × Nat :=
  (List.range 16).foldl (fun acc j =>
      if x.1.testBit j then lmul dat.beta acc ((dat.uConjL.getD k []).getD j (0, 0)) else acc)
    (0, colsAct (dat.uConjT.getD k []) x.2)

@[expose] def conjkap (dat : Data) (κ : Nat) (x : Nat × Nat) : Nat × Nat :=
  (List.range 10).foldr (fun k y => if κ.testBit k then conjk dat k y else y) x

@[expose] def moveleftR (dat : Data) (k : Nat) : List Nat → Nat × Nat
  | [] => (0, 0)
  | c :: rest =>
    let X := (dat.uComm.getD c []).getD k (0, 0)
    lmul dat.beta (rest.foldl (fun x c2 => conjk dat c2 x) X) (moveleftR dat k rest)

@[expose] def rmulU (dat : Data) (g : (Nat × Nat) × Nat) (k : Nat) : (Nat × Nat) × Nat :=
  let P := (List.range k).filter g.2.testBit
  let Q := (List.range 10).filter fun c => k < c && g.2.testBit c
  let Y := moveleftR dat k Q.reverse
  if g.2.testBit k then
    let z := lmul dat.beta (conjk dat k Y) (dat.uSq.getD k (0, 0))
    (lmul dat.beta g.1 (P.reverse.foldl (fun y c => conjk dat c y) z), g.2 ^^^ 2 ^ k)
  else
    (lmul dat.beta g.1 (P.reverse.foldl (fun y c => conjk dat c y) Y), g.2 ||| 2 ^ k)

@[expose] def pmul (dat : Data) (g h : (Nat × Nat) × Nat) : (Nat × Nat) × Nat :=
  ((List.range 10).filter h.2.testBit).foldl (rmulU dat)
    (lmul dat.beta g.1 (conjkap dat g.2 h.1), g.2)


end MonsterB.P0Rank
