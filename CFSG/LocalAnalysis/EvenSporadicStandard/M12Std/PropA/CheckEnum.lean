module

public import CFSG.Sporadic.SmallOddCore.CentSpec
public import Certificates.Data.CFSGNative.PropA.Check

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv Subgroup CFSG.Sporadic CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.M12Std.PropA.Native

variable {n : ℕ}

structure Enum (n : ℕ) (E : List Table) (S : Set (Perm (Fin n))) : Prop where
  forall₂ : ∃ ps : List (Perm (Fin n)),
    List.Forall₂ (Th.Rep n) E ps ∧ ps.Nodup ∧ ∀ g, g ∈ ps ↔ g ∈ S

theorem Enum.card {E : List Table} {S : Set (Perm (Fin n))} (h : Enum n E S) :
    Nat.card S = E.length := by
  obtain ⟨ps, h2, hnd, hmem⟩ := h
  have hS : S = (ps.toFinset : Set (Perm (Fin n))) := by
    ext g
    rw [← hmem g]
    simp [List.mem_toFinset]
  rw [hS, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd,
    h2.length_eq]


private theorem forall₂_filter {E : List Table} {ps : List (Perm (Fin n))}
    {f : Table → Bool} {P : Perm (Fin n) → Prop} [DecidablePred P]
    (hf : ∀ T g, Th.Rep n T g → (f T = true ↔ P g))
    (h : List.Forall₂ (Th.Rep n) E ps) :
    List.Forall₂ (Th.Rep n) (E.filter f) (ps.filter fun g => decide (P g)) :=
  List.rel_filter (R := Th.Rep n) (p := f) (q := fun g => decide (P g))
    (fun T g hT => (hf T g hT).trans (iff_of_eq (decide_eq_true_eq (p := P g))).symm) h


theorem Enum.filter {E : List Table} {S : Set (Perm (Fin n))} (h : Enum n E S)
    {f : Table → Bool} {P : Perm (Fin n) → Prop}
    (hf : ∀ T g, Th.Rep n T g → (f T = true ↔ P g)) :
    Enum n (E.filter f) {g | g ∈ S ∧ P g} := by
  classical
  obtain ⟨ps, h2, hnd, hmem⟩ := h
  refine ⟨ps.filter fun g => decide (P g), forall₂_filter hf h2, hnd.filter _, ?_⟩
  intro g
  rw [List.mem_filter, hmem g, decide_eq_true_eq]
  rfl


theorem gensP_spec {gs : Array Table} (h : gensP n gs = true) :
    ∀ x ∈ gs, permOK n x = true ∧ invOK n x (invT n x) = true := by
  rw [gensP, Array.all_eq_true'] at h
  intro x hx
  have hx' := h x hx
  rw [Bool.and_eq_true_iff] at hx'
  exact hx'


theorem closedOK_of_closedHOK {gens L : Array Table} (h : closedHOK n gens L = true) :
    closedOK n gens L = true := by
  rw [closedOK, Array.all_eq_true']
  simp only [closedHOK] at h
  rw [Array.all_eq_true'] at h
  intro x hx
  rw [Array.all_eq_true']
  intro g hg
  have hxg := h x hx
  rw [Array.all_eq_true'] at hxg
  have hxg' := hxg g hg
  rw [memT, Array.any_eq_true']
  split at hxg'
  · rename_i i _
    rw [Bool.and_eq_true_iff, decide_eq_true_eq, tblEq_iff] at hxg'
    exact ⟨L[i]!, getElem!_mem_array hxg'.1, by
      rw [tblEq_iff]
      intro j hj
      exact (hxg'.2 j hj).symm⟩
  · exact Bool.noConfusion hxg'

theorem enumP_spec (hn : n < 2 ^ 32) {cap N : ℕ} {gs : Array Table}
    (h : enumP n cap gs N = true) :
    Enum n (mulClosureH n gs cap).1.toList ↑(closure (tp n '' {x | x ∈ gs})) ∧
      (mulClosureH n gs cap).1.size = N := by
  rw [enumP] at h
  simp only [Bool.and_eq_true, Bool.and_eq_true_iff, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hgens, htree⟩, hclosed⟩, hdist⟩, hsize⟩ := h
  have hgspec := gensP_spec hgens
  have hg : ∀ x ∈ gs, permOK n x = true := fun x hx => (hgspec x hx).1
  have hginv : ∀ x ∈ gs, invOK n x (invT n x) = true := fun x hx => (hgspec x hx).2
  obtain ⟨hErep, hcov, -⟩ :=
    enum_spec hn hg hginv htree (closedOK_of_closedHOK hclosed) hdist
  have hE : ∀ k < (mulClosureH n gs cap).1.size,
      Th.Rep n (mulClosureH n gs cap).1[k]! (tablePerm n (mulClosureH n gs cap).1[k]!) :=
    fun k hk => (hErep k hk).1
  refine ⟨⟨(mulClosureH n gs cap).1.toList.map (tablePerm n), ?_, ?_, ?_⟩, hsize⟩
  · exact forall₂_tablePerm hE
  · exact nodup_of_hkeysDistinct (forall₂_tablePerm hE) hdist
  · intro g
    constructor
    · intro hgm
      obtain ⟨k, hk, hgk⟩ := mem_map_tablePerm hE hgm
      rw [hgk]
      exact (hErep k hk).2
    · intro hg
      obtain ⟨k, hk, hrep⟩ := hcov g hg
      exact List.mem_map.mpr ⟨(mulClosureH n gs cap).1[k]!,
        Array.mem_toList_iff.mpr (getElem!_mem_array hk), tablePerm_eq hrep⟩


end CFSG.EvenSporadicStandard.M12Std.PropA
