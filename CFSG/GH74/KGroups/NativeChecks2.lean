module

public import CFSG.GH74.KGroups.NativeChecks
public import Certificates.Data.CFSGNative.KGroups.Enum

public section

namespace CFSG.GH74.KGroups.NativeChecks

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KGroups.Native CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.GH74.KGroups

variable {n : ℕ}

theorem toA_mul (σ τ : Equiv.Perm (Fin n)) : compA n (toA σ) (toA τ) = toA (σ * τ) := by
  have h : ∀ i : Fin n, (toA σ)[(toA τ)[i.val]!]! = ((σ * τ) i : ℕ) := fun i => by
    rw [← compA_get i.2]
    exact rep_compA (rep_toA σ) (rep_toA τ) i
  rw [compA]
  exact congrArg (Array.ofFn (n := n)) (funext h)

theorem idA_eq_toA : idA n = toA (1 : Equiv.Perm (Fin n)) := rfl

theorem productsA_map_toA (Ts : List (List (Equiv.Perm (Fin n)))) :
    productsA n (Ts.map (List.map toA)) = (products Ts).map toA := by
  induction Ts with
  | nil => simp only [List.map_nil, productsA, products, List.map_cons, idA_eq_toA]
  | cons T Ts ih =>
    simp only [List.map_cons, productsA, products, ih, List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun t _ => ?_
    simp only [List.map_map]
    exact List.map_congr_left fun x _ => toA_mul t x

@[expose] def levelsA (Q : RawSchreierDatum n) : List (List (Array ℕ)) :=
  (List.finRange Q.baseCount).map fun i => (levelTransversals Q i).map toA

@[expose] def enumA (Q : RawSchreierDatum n) : List (Array ℕ) := productsA n (levelsA Q)

theorem enumA_eq (Q : RawSchreierDatum n) : enumA Q = (elemsT Q).map toA := by
  rw [elemsT_eq, enumeration, ← productsA_map_toA, List.map_map]
  rfl

@[expose] def elemsTab (Q : RawSchreierDatum n) : List (Equiv.Perm (Fin n)) :=
  (products ((List.finRange Q.baseCount).map fun i => (levelTransversals Q i).map tab)).map tab

theorem elemsTab_eq (Q : RawSchreierDatum n) : elemsTab Q = elemsT Q := by
  have h : (tab : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) = id := funext tab_eq
  simp only [elemsTab, elemsT, enumeration, h, List.map_id]

theorem centTrivCheck_enumA (Q : RawSchreierDatum n) (a b : Equiv.Perm (Fin n)) :
    centTrivCheck (elemsT Q) a b = centTrivA n (enumA Q) (toA a) (toA b) := by
  rw [centTrivCheck_eq, enumA_eq]

@[expose] def pairCountE (Q : RawSchreierDatum n) (oa ob : ℕ) (ws : List (List Bool × ℕ)) : ℕ :=
  countPairsA n ws ((enumA Q).filter fun a => orderIsA n a oa)
    ((enumA Q).filter fun a => orderIsA n a ob)

theorem pairCountB_eq_E (Q : RawSchreierDatum n) (oa ob : ℕ) (ws : List (List Bool × ℕ)) :
    pairCountB Q oa ob ws = pairCountE Q oa ob ws := by
  rw [pairCountB_eq]
  unfold pairCountN pairCountE
  rw [enumA_eq]


end CFSG.GH74.KGroups.NativeChecks
