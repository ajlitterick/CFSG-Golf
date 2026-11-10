module

public section

namespace CFSG.OddStandard.Solomon75.AhatData

@[expose] def idA (n : Nat) : Array Nat := Array.ofFn (n := n) fun i => i.val

@[expose] def mulA (n : Nat) (t u : Array Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => t[u[i.val]!]!

@[expose] def eqA (n : Nat) (t u : Array Nat) : Bool := Nat.all n fun i _ => t[i]! == u[i]!

@[expose] def suppAux (t : Array Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => suppAux t k + (if t[k]! == k then 0 else 1)

@[expose] def suppA (n : Nat) (t : Array Nat) : Nat := suppAux t n

@[expose] def swapA (n a b : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => if i.val == a then b else if i.val == b then a else i.val

@[expose] def swapsA (n : Nat) (sw : List (Nat × Nat)) : Array Nat :=
  sw.foldl (fun t p => mulA n t (swapA n p.1 p.2)) (idA n)

@[expose] def commA (n : Nat) (a b : Array Nat) : Bool := eqA n (mulA n a b) (mulA n b a)

@[expose] def isoA (n : Nat) (t : Array Nat) : Bool :=
  eqA n (mulA n t t) (idA n) && suppA n t == 8

@[expose] def dblA (n : Nat) (t : Array Nat) : Bool :=
  eqA n (mulA n t t) (idA n) && suppA n t == 4

@[expose] def adjA (n : Nat) (a b : Array Nat) : Bool :=
  !(eqA n a b) && commA n a b && isoA n (mulA n a b)

@[expose] def genSwaps (n : Nat) : List (List (Nat × Nat)) :=
  if n ≤ 9 then
    [[(4, 6), (5, 7)], [(2, 3), (6, 7)], [(0, 4), (1, 5), (2, 6), (3, 7)]]
  else
    [[(6, 7), (8, 9)], [(4, 6), (5, 7)], [(0, 4), (1, 5), (2, 6), (3, 7)]]

@[expose] def gensA (n : Nat) : Array (Array Nat) := (genSwaps n).toArray.map (swapsA n)


@[expose] def invOK (n : Nat) (tab : Array (Array Nat)) (inv : Array Nat) : Bool :=
  inv.size == tab.size &&
  Nat.all tab.size fun k _ => decide (inv[k]! < tab.size) &&
    eqA n (mulA n tab[k]! tab[inv[k]!]!) (idA n)

@[expose] def isoIdx (n : Nat) (tab : Array (Array Nat)) : Array Nat :=
  (Array.range tab.size).filter fun k => isoA n tab[k]!

@[expose] def nbrOK (n : Nat) (tab : Array (Array Nat)) : Bool :=
  (isoIdx n tab).all fun k => (isoIdx n tab).any fun l => adjA n tab[k]! tab[l]!


@[expose] def connOK (n : Nat) (tab : Array (Array Nat)) (ord : Array Nat) : Bool :=
  let I := isoIdx n tab
  decide (0 < I.size) && ord[0]! == 0 && Nat.all I.size (fun i _ => ord.contains i) &&
  Nat.all ord.size fun k _ => decide (ord[k]! < I.size) &&
    (k == 0 || Nat.any k fun j _ => adjA n tab[I[ord[j]!]!]! tab[I[ord[k]!]!]!)

@[expose] def rankOK (n : Nat) (tab : Array (Array Nat)) : Bool :=
  let I := (isoIdx n tab).map fun k => tab[k]!
  I.all fun a => I.all fun b => !(commA n a b && isoA n (mulA n a b)) ||
    I.all fun c => !(commA n a c && commA n b c && isoA n (mulA n a c) && isoA n (mulA n b c) &&
        isoA n (mulA n (mulA n a b) c)) ||
      I.all fun d => !(commA n a d && commA n b d && commA n c d &&
        isoA n (mulA n a d) && isoA n (mulA n b d) && isoA n (mulA n c d) &&
        isoA n (mulA n (mulA n a b) d) && isoA n (mulA n (mulA n a c) d) &&
        isoA n (mulA n (mulA n b c) d) && isoA n (mulA n (mulA n (mulA n a b) c) d))

@[expose] def eightArr (n : Nat) (a b c : Array Nat) : Array (Array Nat) :=
  #[idA n, a, b, mulA n a b, c, mulA n a c, mulA n b c, mulA n (mulA n a b) c]

@[expose] def eightSubOK (n : Nat) (a b c : Array Nat) : Bool :=
  let E := eightArr n a b c
  (Nat.all 8 fun i _ => Nat.all 8 fun j _ => E.any fun z => eqA n (mulA n E[i]! E[j]!) z) &&
    Nat.all 8 fun i _ => Nat.all i fun j _ => !(eqA n E[i]! E[j]!)

@[expose] def eightOK (n : Nat) (tab : Array (Array Nat)) : Bool :=
  let I := (isoIdx n tab).map fun k => tab[k]!
  I.any fun a => I.any fun b => commA n a b && isoA n (mulA n a b) &&
    I.any fun c => commA n a c && commA n b c && isoA n (mulA n a c) && isoA n (mulA n b c) &&
        isoA n (mulA n (mulA n a b) c) && eightSubOK n a b c

@[expose] def halfOK (n : Nat) (tab : Array (Array Nat)) : Bool :=
  (isoIdx n tab).any fun k =>
    (Nat.all tab.size fun j _ => commA n tab[k]! tab[j]!) &&
    tab.any fun s => dblA n s && commA n s tab[k]! && isoA n (mulA n s tab[k]!)


end CFSG.OddStandard.Solomon75.AhatData
