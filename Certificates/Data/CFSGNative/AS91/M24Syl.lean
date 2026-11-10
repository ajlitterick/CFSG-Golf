module

public import Certificates.Data.CFSGNative.AS91.M24Todd

public section

set_option compiler.extract_closed false

namespace CFSG.Quasithin.H13.AS91.M24G.Native

@[expose] def treeValid {α : Type} [Inhabited α] [DecidableEq α] (valid : α → Bool)
    (steps : List (α → α)) (base : α) (r : Array α × Array Nat × Array Nat) : Bool :=
  decide (0 < r.1.size) && decide (r.1[0]! = base) && r.2.1.size == r.1.size &&
    r.2.2.size == r.1.size &&
    allLt r.1.size fun j => valid r.1[j]! && (j == 0 || (decide (r.2.1[j]! < j) &&
      decide (r.2.2[j]! < steps.length) &&
      decide ((steps.getD r.2.2[j]! id) r.1[r.2.1[j]!]! = r.1[j]!)))

@[expose] def s0Tabs : List (Array Nat) :=
  [#[0, 1, 2, 3, 7, 6, 5, 4, 14, 15, 12, 13, 9, 8, 11, 10, 23, 22, 21, 20, 16, 17, 18, 19],
    #[4, 5, 6, 7, 1, 0, 3, 2, 12, 13, 14, 15, 9, 8, 11, 10, 18, 19, 16, 17, 23, 22, 21, 20],
    #[4, 5, 7, 6, 1, 0, 2, 3, 12, 13, 15, 14, 9, 8, 10, 11, 23, 22, 20, 21, 18, 19, 17, 16],
    #[4, 5, 7, 6, 1, 0, 2, 3, 20, 21, 23, 22, 17, 16, 18, 19, 15, 14, 12, 13, 10, 11, 9, 8]]

@[expose] def pairPart : List Nat := [3, 12, 48, 192]


@[expose] def imgTriple (g : Array Nat) (x : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (g[x.1]!, g[x.2.1]!, g[x.2.2]!)

@[expose] def keyTriple (x : Nat × Nat × Nat) : Nat := x.1 + 24 * (x.2.1 + 24 * x.2.2)

@[expose] def validTriple (x : Nat × Nat × Nat) : Bool :=
  decide (x.1 < 24) && decide (x.2.1 < 24) && decide (x.2.2 < 24)


abbrev OSP : Type := Nat × List Nat × List Nat

@[expose] def imgOSP (g : Array Nat) (x : OSP) : OSP :=
  (img g x.1, imgSext g x.2.1, imgSext g x.2.2)

@[expose] def keyOSP (x : OSP) : Nat := (x.1 <<< 240) ||| (keyL x.2.1 <<< 96) ||| keyL x.2.2

@[expose] def validOSP (x : OSP) : Bool :=
  decide (x.1 < 2 ^ 24) && x.2.1.all (fun m => decide (m < 2 ^ 24)) &&
    x.2.2.all (fun m => decide (m < 2 ^ 24)) && decide (x.2.1.Pairwise (· < ·)) &&
    decide (x.2.2.Pairwise (· < ·))

@[expose] def tup0 : OSP := (255, baseSext, pairPart)


@[expose] def clsOf (s : List Nat) : Nat := actM ccEColsN (s.headD 0)

@[expose] def clsTab (S : Array (List Nat)) : Array Nat := S.map clsOf


@[expose] def sextsThrough (S : Array (List Nat)) (t : Nat × Nat × Nat) : List Nat :=
  (List.range nSext).filter fun q => trioIn t S[q]!


@[expose] def v0List : List Nat := [0, 31, 160, 191, 320, 351, 480, 511]

@[expose] def vpList : List Nat := [0, 31, 224, 255, 320, 351, 416, 447]

@[expose] def closedXor (L : List Nat) : Bool := L.all fun a => L.all fun b => L.contains (a ^^^ b)


@[expose] def scTab (cl : Array Nat) : Array Bool :=
  (Array.range 2048).map fun m => cl.toList.contains m

@[expose] def sp8 (v w : Nat) : List Nat :=
  [0, 31, v, 31 ^^^ v, w, 31 ^^^ w, v ^^^ w, 31 ^^^ v ^^^ w]


@[expose] def stepSp (a : Array Nat) (L : List Nat) : List Nat := sortL (L.map (toddAct a))

@[expose] def keySp (L : List Nat) : Nat := L.foldl (fun acc m => (acc <<< 11) ||| m) 0

@[expose] def validSp (L : List Nat) : Bool :=
  L.all (fun m => decide (m < 2048)) && decide (L.Pairwise (· < ·)) && closedXor L &&
    L.contains 0


end CFSG.Quasithin.H13.AS91.M24G.Native
