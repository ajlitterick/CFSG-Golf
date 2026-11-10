module

public import CFSG.YGroups.DCE.PermBSpec
public import Certificates.Data.CFSGNative.YGroups.DCE.EngineB
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def forestRec (n : ℕ) (G : Array ByteArray) :
    Array ℕ × Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut pos : Array ℕ := Array.replicate n n
  let mut tp : Array ℕ := Array.replicate n n
  let mut tl : Array ℕ := Array.replicate n 0
  let mut rt : Array ℕ := Array.replicate n n
  let mut off := 0
  for s in [0:n] do
    if rt[s]! == n then
      let r := B.orbitRec n s G
      for y in r.1 do
        pos := pos.set! y (off + r.2.1[y]!)
        tp := tp.set! y r.2.2.1[y]!
        tl := tl.set! y r.2.2.2[y]!
        rt := rt.set! y s
      off := off + r.1.size
  return (pos, tp, tl, rt)

@[expose] def forestValid (n : ℕ) (G : Array ByteArray)
    (f : Array ℕ × Array ℕ × Array ℕ × Array ℕ) : Bool :=
  allLt n fun x =>
    decide (f.2.2.2[x]! < n) && f.2.2.2[f.2.2.2[x]!]! == f.2.2.2[x]! &&
      (f.2.2.2[x]! == x ||
        (decide (f.2.2.1[x]! < G.size) && decide (f.2.1[x]! < n) &&
          decide (f.1[f.2.1[x]!]! < f.1[x]!) && f.2.2.2[f.2.1[x]!]! == f.2.2.2[x]! &&
          bget G[f.2.2.1[x]!]! f.2.1[x]! == x))


theorem index_mul_card_map_of_ker_le {E G' : Type*} [Group E] [Group G'] [Finite E]
    (φ : E →* G') (P : Subgroup E) (hker : φ.ker ≤ P) :
    P.index * Nat.card (P.map φ) = Nat.card φ.range := by
  have h1 : (P.map φ).relIndex φ.range = P.index := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
      Subgroup.relIndex_top_right, sup_of_le_left hker]
  have h2 := Subgroup.relIndex_mul_card (H := P.map φ) (K := φ.range)
  rwa [inf_of_le_left (Subgroup.map_le_range φ P), h1] at h2

