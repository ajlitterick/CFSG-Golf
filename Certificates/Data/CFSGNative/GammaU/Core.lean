module

public import Std.Data.HashSet

public section

set_option compiler.extract_closed false

namespace CFSG.GammaU.Native

@[expose] def q0b (n : Nat) : Bool :=
  (List.range 6).foldl (fun acc i => acc ^^ (n.testBit i || n.testBit (i + 6))) false

@[expose] def theta0N (n : Nat) : Nat := (n >>> 6) ||| (((n &&& 63) ^^^ (n >>> 6)) <<< 6)

@[expose] def appN (rows : Array Nat) (n : Nat) : Nat :=
  let a0 := if n.testBit 0 then 0 ^^^ rows[0]! else 0
  let a1 := if n.testBit 1 then a0 ^^^ rows[1]! else a0
  let a2 := if n.testBit 2 then a1 ^^^ rows[2]! else a1
  let a3 := if n.testBit 3 then a2 ^^^ rows[3]! else a2
  let a4 := if n.testBit 4 then a3 ^^^ rows[4]! else a3
  let a5 := if n.testBit 5 then a4 ^^^ rows[5]! else a4
  let a6 := if n.testBit 6 then a5 ^^^ rows[6]! else a5
  let a7 := if n.testBit 7 then a6 ^^^ rows[7]! else a6
  let a8 := if n.testBit 8 then a7 ^^^ rows[8]! else a7
  let a9 := if n.testBit 9 then a8 ^^^ rows[9]! else a8
  let a10 := if n.testBit 10 then a9 ^^^ rows[10]! else a9
  if n.testBit 11 then a10 ^^^ rows[11]! else a10

@[expose] def f0b (m n : Nat) : Bool :=
  (List.range 6).foldl
    (fun acc i => acc ^^ ((m.testBit i && n.testBit (6 + i)) ^^ (m.testBit (6 + i) && n.testBit i)))
    false

@[expose] def spanList : List Nat → List Nat
  | [] => [0]
  | v :: vs => spanList vs ++ (spanList vs).map (· ^^^ v)


@[expose] def bfsRound {σ κ : Type} [BEq κ] [Hashable κ] (key : σ → κ) (fs : List (σ → σ))
    (frontier : List σ) (seen : Std.HashSet κ) : List σ × Std.HashSet κ :=
  (frontier.flatMap fun s => fs.map fun f => f s).foldl
    (fun (acc : List σ × Std.HashSet κ) t =>
      match acc with
      | (l, h) => if h.contains (key t) then (l, h) else (t :: l, h.insert (key t)))
    ([], seen)

@[expose] def bfsClosure {σ κ : Type} [BEq κ] [Hashable κ] (key : σ → κ) (fs : List (σ → σ)) :
    Nat → List σ → Std.HashSet κ → List σ → List σ
  | 0, frontier, _, visited => frontier ++ visited
  | fuel + 1, frontier, seen, visited =>
    let r := bfsRound key fs frontier seen
    if r.1.isEmpty then frontier ++ visited
    else bfsClosure key fs fuel r.1 r.2 (frontier ++ visited)


@[expose] def a0 : Nat := 3072

@[expose] def gamuGens : List (Array Nat) :=
  [#[1, 2, 32, 8, 16, 4, 64, 128, 2048, 512, 1024, 256],
    #[2, 4, 1112, 1097, 32, 25, 128, 256, 593, 1553, 2048, 1600],
    #[64, 2, 4, 8, 16, 32, 65, 128, 256, 512, 1024, 2048],
    #[1, 2, 4, 8, 16, 32, 65, 130, 260, 520, 1040, 2080]]

@[expose] def saGens : List (Array Nat) :=
  [#[952, 269, 3463, 3833, 2201, 1193, 3638, 841, 497, 3650, 1659, 2683],
    #[3778, 3961, 444, 3270, 413, 429, 3707, 317, 3718, 3443, 1734, 2758]]


@[expose] def d0 : List Nat := [961, 48, 9, 5, 3, 3072]

@[expose] def ws : List Nat := [3072, 1, 2, 4, 8, 16]


@[expose] def k0 : Array Nat := #[1, 2, 4, 8, 32, 16, 64, 128, 256, 512, 2048, 1024]

@[expose] def cBasis : List (Array Nat) :=
  [#[1, 2, 3076, 3080, 796, 812, 64, 128, 3376, 3632, 1036, 2060],
    #[1, 3074, 4, 3080, 666, 682, 64, 3248, 256, 3632, 1034, 2058],
    #[3073, 2, 4, 3080, 601, 617, 3184, 128, 256, 3632, 1033, 2057],
    #[49, 50, 52, 3128, 535, 551, 3136, 3200, 3328, 560, 1992, 3016],
    #[14, 13, 11, 7, 1040, 2080, 910, 845, 715, 455, 1024, 2048]]

@[expose] def idR : Array Nat := #[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

@[expose] def mulR (g h : Array Nat) : Array Nat := h.map (appN g)

@[expose] def isoN (r : Array Nat) : Bool :=
  r.size == 12 && r.all (· < 4096) && (List.range 4096).all fun n => q0b (appN r n) == q0b n

@[expose] def unitaryN (r : Array Nat) : Bool :=
  (List.range 12).all fun j => appN r (theta0N (2 ^ j)) == theta0N (appN r (2 ^ j))

@[expose] def antiN (r : Array Nat) : Bool :=
  (List.range 12).all fun j => appN r (theta0N (2 ^ j)) == theta0N (theta0N (appN r (2 ^ j)))

@[expose] def gammaUN (r : Array Nat) : Bool := isoN r && (unitaryN r || antiN r)


@[expose] def subsetProducts (gens : List (Array Nat)) : List (Array Nat) :=
  gens.foldl (fun acc g => acc ++ acc.map (mulR g)) [idR]

@[expose] def compOf (c : Nat) : List (Array Nat) :=
  subsetProducts ((List.range 5).map fun i =>
    if c.testBit i then mulR k0 cBasis[i]! else cBasis[i]!)


@[expose] def gamuInv : List (Array Nat) :=
  [#[1, 2, 32, 8, 16, 4, 64, 128, 2048, 512, 1024, 256],
    #[804, 1, 2, 44, 808, 16, 2572, 64, 128, 2816, 2316, 1024],
    #[65, 2, 4, 8, 16, 32, 1, 128, 256, 512, 1024, 2048],
    #[1, 2, 4, 8, 16, 32, 65, 130, 260, 520, 1040, 2080]]

@[expose] def saInv : List (Array Nat) :=
  [#[574, 3908, 454, 635, 2841, 1833, 4022, 313, 385, 3826, 1653, 2677],
    #[761, 3956, 3466, 245, 733, 749, 3211, 637, 3894, 3459, 1419, 2443]]


@[expose] def compGens (c : Nat) : List (Array Nat) :=
  (List.range 5).map fun i => if c.testBit i then mulR k0 cBasis[i]! else cBasis[i]!

@[expose] def colPts (s : Array Nat) : List Nat :=
  let S := spanList d0
  let im := (List.range 4096).map fun n => appN s n ^^^ n
  S.filter fun e => e != 0 && !q0b e && e != a0 && e != theta0N a0 &&
    e != (a0 ^^^ theta0N a0) && im.contains e

@[expose] def unitaryElts (i : Nat) : List (Array Nat) :=
  (compOf i).filter fun s => s != idR && unitaryN s


@[expose] def orbitOf (gens : List (Array Nat)) (p : Nat) : List Nat :=
  bfsClosure id (gens.map appN) 4096 [p] ((∅ : Std.HashSet Nat).insert p) []

@[expose] def closedCheck (gs X : List (Array Nat)) : Bool :=
  let S := Std.HashSet.ofList X
  X.all fun x => gs.all fun g => S.contains (mulR x g)


@[expose] def pairsOK (_ : Unit := ()) : Bool :=
  gamuGens.length == gamuInv.length && saGens.length == saInv.length &&
    ((gamuGens.zip gamuInv).all fun (g, gi) =>
      gammaUN g && gammaUN gi && mulR g gi == idR && mulR gi g == idR) &&
    (saGens.zip saInv).all fun (g, gi) =>
      gammaUN g && gammaUN gi && mulR g gi == idR && mulR gi g == idR && appN g a0 == a0


@[expose] def closedOrbit (O : List Nat) (gens : List (Array Nat)) : Bool :=
  let H := Std.HashSet.ofList O
  O.all fun x => gens.all fun g => H.contains (appN g x)


end CFSG.GammaU.Native
