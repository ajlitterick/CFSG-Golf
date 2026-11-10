module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native


theorem size_subgroupList_of_enumW {cap m : ℕ} {ws : List (List ℕ)} (h : enumW cap m ws = true) :
    (subgroupList cap ws).size = m := by
  simp only [enumW, enumOKH, Bool.and_eq_true, beq_iff_eq] at h
  simpa only [subgroupList] using h.2.2

theorem IsEnumSet.filter {n : ℕ} {E : Array Table} {S : Set (Equiv.Perm (Fin n))}
    (h : IsEnumSet n E S) (b : Table → Bool) (Q : Equiv.Perm (Fin n) → Prop)
    (hb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g → (b x = true ↔ Q g)) :
    IsEnumSet n (E.filter b) {g : Equiv.Perm (Fin n) | g ∈ S ∧ Q g} := by
  constructor
  · intro k hk
    have hmem : (E.filter b)[k]! ∈ E.filter b := getElem!_mem_array hk
    rw [Array.mem_filter] at hmem
    obtain ⟨hmemE, hbtrue⟩ := hmem
    obtain ⟨j, hj, hjE⟩ := Array.getElem_of_mem hmemE
    obtain ⟨g, hgS, hrep⟩ := h.rep j hj
    have hjt : (E.filter b)[k]! = E[j]! := by
      rw [getElem!_pos E j hj, ← hjE]
    have hrep' : Rep n (E.filter b)[k]! g := by rw [hjt]; exact hrep
    exact ⟨g, ⟨hgS, (hb (E.filter b)[k]! g hrep').1 hbtrue⟩, hrep'⟩
  · intro g hg
    obtain ⟨hgS, hQg⟩ := hg
    obtain ⟨j, hj, hrep⟩ := h.cov g hgS
    have hbj : b E[j]! = true := (hb (E[j]!) g hrep).2 hQg
    have hmemf : E[j]! ∈ E.filter b := by
      rw [Array.mem_filter]
      exact ⟨getElem!_mem_array hj, hbj⟩
    obtain ⟨k, hk, hkE⟩ := Array.getElem_of_mem hmemf
    refine ⟨k, hk, ?_⟩
    have hkt : (E.filter b)[k]! = E[j]! := by
      rw [getElem!_pos (E.filter b) k hk, hkE]
    rw [hkt]; exact hrep


end CFSG.EvenSporadicStandard.HNRecog
