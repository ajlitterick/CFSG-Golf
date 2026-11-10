module

public import CFSG.Sporadic.Recognition.McLASInputs

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

variable {n : ℕ}

structure ElemFacts (n : ℕ) (P : Subgroup (Equiv.Perm (Fin n))) (p : ℕ) (r : ElemRow) : Prop where
  rep : Rep n r.rep (tp n r.rep)
  order : orderOf (tp n r.rep) = p
  mem : tp n r.rep ∈ P
  gens : closure (tp n '' {x | x ∈ r.centGens.toArray}) =
    P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))
  cent : Nat.card ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = r.centOrder
  cls : (conjClass P (tp n r.rep)).ncard = r.classSize


theorem mem_of_nodup_of_ncard_le {S : Set (Equiv.Perm (Fin n))} {L : List (Equiv.Perm (Fin n))}
    (hL : L.Nodup) (hS : ∀ x ∈ L, x ∈ S) (hlen : S.ncard ≤ L.length) : ∀ y ∈ S, y ∈ L := by
  classical
  have hsub : (L.toFinset : Set (Equiv.Perm (Fin n))) ⊆ S := fun x hx =>
    hS x (List.mem_toFinset.mp hx)
  have hcard : S.ncard ≤ (L.toFinset : Set (Equiv.Perm (Fin n))).ncard := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]
    exact hlen
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  intro y hy
  have : y ∈ (L.toFinset : Set (Equiv.Perm (Fin n))) := by rw [heq]; exact hy
  exact List.mem_toFinset.mp this

theorem conjClosure_cover {P : Subgroup (Equiv.Perm (Fin n))} {pg pgInv : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool} (hD : GroupData n P pg gg sift)
    (hpgi : ∀ l < pg.size, Rep n pgInv[l]! (gg l)⁻¹) {t : Table} {tg : Equiv.Perm (Fin n)}
    (hT : Rep n t tg) {o : Closure} (horb : conjTreeOK n pg pgInv t o.1 o.2.1 o.2.2 = true)
    (hdist : hkeysDistinct n o.1.toList = true) (hsize : (conjClass P tg).ncard ≤ o.1.size) :
    (∀ k < o.1.size, ∃ c ∈ P, Rep n o.1[k]! (c * tg * c⁻¹)) ∧
      ∀ y ∈ conjClass P tg, ∃ k < o.1.size, Rep n o.1[k]! y := by
  have hgP : ∀ l < pg.size, Rep n pg[l]! (gg l) ∧ Rep n pgInv[l]! (gg l)⁻¹ ∧ gg l ∈ P :=
    fun l hl => ⟨hD.rep l hl, hpgi l hl, hD.mem hl⟩
  have horb' := conjTreeOK_spec P hgP hT horb
  refine ⟨horb', fun y hy => ?_⟩
  have horep : ∀ k < o.1.size, Rep n o.1[k]! (tablePerm n o.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := horb' k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have honodup := nodup_of_hkeysDistinct (forall₂_tablePerm horep) hdist
  have hmem := mem_of_nodup_of_ncard_le honodup (S := conjClass P tg)
    (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hx
      obtain ⟨c, hc, hrep⟩ := horb' k hk
      rw [tablePerm_eq hrep]
      exact ⟨c, hc, rfl⟩)
    (by rw [List.length_map, Array.length_toList]; exact hsize) y hy
  obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hmem
  exact ⟨k, hk, horep k hk⟩

end CFSG.Sporadic.Recognition.McLAS
