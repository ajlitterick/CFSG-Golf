module

public import CFSG.YGroups.DCE.PermBSpec
public import CFSG.YGroups.DoubleCosetPoints
public import Certificates.Data.CFSGNative.YGroups.DCE.EngineB
public import Batteries.Data.ByteArray

public section

namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def recValidN (n β : ℕ) (gens : Array ByteArray)
    (r : Array ℕ × Array ℕ × Array ℕ × Array ℕ) : Bool :=
  decide (β < n) && r.2.1.size == n && r.1.size != 0 && r.1[0]! == β &&
    allLt r.1.size fun t =>
      let x := r.1[t]!
      decide (x < n) && r.2.1[x]! == t &&
        (t == 0 || (decide (r.2.2.2[x]! < gens.size) && decide (r.2.2.1[x]! < n) &&
          decide (r.2.1[r.2.2.1[x]!]! < t) && r.1[r.2.1[r.2.2.1[x]!]!]! == r.2.2.1[x]! &&
          bget gens[r.2.2.2[x]!]! r.2.2.1[x]! == x))

@[expose] def recMemN (n : ℕ) (r : Array ℕ × Array ℕ × Array ℕ × Array ℕ) (x : ℕ) : Bool :=
  decide (x < n) && decide (r.2.1[x]! < r.1.size) && r.1[r.2.1[x]!]! == x


section Exact

variable {n : ℕ} {S : Subgroup (Equiv.Perm (Fin n))} {k : ℕ} {β : ℕ → Fin n}
  {gens : ℕ → Array ByteArray}
  (hgen : ∀ l < k, ∀ i < (gens l).size,
    ∃ g ∈ S, RepB n (gens l)[i]! g ∧ ∀ m < l, g (β m) = β m)
  (hrec : ∀ l < k, recValidN n (β l) (gens l) (B.orbitRec n (β l) (gens l)) = true)
  (hcard : Nat.card S ≤ ∏ l ∈ Finset.range k, (B.orbitRec n (β l) (gens l)).1.size)

include hgen hrec hcard


end Exact

@[expose] def siftLevel (n β : ℕ) (gens : Array ByteArray)
    (r : Array ℕ × Array ℕ × Array ℕ × Array ℕ) : ℕ → ByteArray → Option ByteArray
  | 0, _ => none
  | fuel + 1, σ =>
    let x := bget σ β
    if recMemN n r x then
      if x = β then some σ
      else siftLevel n β gens r fuel (bcomp n (binvCand n gens[r.2.2.2[x]!]!) σ)
    else none

@[expose] def siftChain (n : ℕ) : List (ℕ × Array ByteArray) → ByteArray → Option ByteArray
  | [], σ => some σ
  | (β, gens) :: levels, σ =>
    match siftLevel n β gens (B.orbitRec n β gens) n σ with
    | some τ => siftChain n levels τ
    | none => none

@[expose] def siftB (n : ℕ) (levels : Array (ℕ × Array ByteArray)) (σ : ByteArray) : Bool :=
  match siftChain n levels.toList σ with
  | some τ => bEq n τ (bid n)
  | none => false


section Sift


end Sift

end CFSG.YGroups.DCE
