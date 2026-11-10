module

public import CFSG.Sporadic.ONOddCore.LiftCands
public import CFSG.Sporadic.ONOddCore.LiftHomCheckInputs

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ON.Native
open CFSG.ComponentClassification.PSL3Four (TabRep)

theorem mem_onMgens_iff
    {g : Equiv.Perm (Fin N)} :
    g ∈ onMgens ↔ ∃ i < 3, g = (hGen i : Equiv.Perm (Fin N)) := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi3 : i < 3 := by rwa [onMgens_length] at hi
    exact ⟨i, hi3, (hGen_val hi3).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [onMgens_length]; exact hi, (hGen_val hi).symm⟩

theorem mem_hGens_iff
    {h : onM} : h ∈ hGens ↔ ∃ i < 3, h = hGen i := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [hGen, List.getD_eq_getElem _ _ hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [hGen, List.getD_eq_getElem _ _ hi]⟩

theorem hGens_closure_top :
    Subgroup.closure {g : onM | g ∈ hGens} = ⊤ := by
  apply Subgroup.map_injective onM.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  conv_rhs => rw [onM]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.coe_subtype, mem_onMgens_iff,
    mem_hGens_iff]
  constructor
  · rintro ⟨h, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hGen i, ⟨i, hi, rfl⟩, rfl⟩

theorem hom_ext_hGens
    {H : Type*} [Group H] {f g : onM →* H}
    (h : ∀ i < 3, f (hGen i) = g (hGen i)) : f = g := by
  apply MonoidHom.eq_of_eqOn_dense hGens_closure_top
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi3 : i < 3 := hi
  have := h i hi3
  rwa [hGen, List.getD_eq_getElem _ _ hi] at this

@[expose] def liftImg
    (e : LiftEntry) (i : ℕ) : onM := evalPos hGens (e.words.getD i [])

theorem lift_form
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    e.words.length = 3 ∧ (∀ w ∈ e.words, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 3) ∧
      (e.power = 1 ∨ e.power = 3) :=
  (r3e_on_local_automorphism_certificate_data.2.2.2.1 _ (recK_mem hk)).2.2 e he

theorem posArr_size_gen (n : ℕ) (gs : Array (Array ℕ)) (w : List ℕ) : (posArr n gs w).size = n := by
  cases w with
  | nil => exact Array.size_ofFn
  | cons l w => exact Array.size_ofFn

theorem posArr_size (gs : Array (Array ℕ)) (w : List ℕ) : (posArr nPts gs w).size = N :=
  posArr_size_gen nPts gs w

theorem prep_liftArrs
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) {i : ℕ}
    (hi : i < 3) :
    PRep N (liftArrs (wordArrs Data.MWords) e)[i]! (liftImg e i : Equiv.Perm (Fin N)) ∧
      (liftArrs (wordArrs Data.MWords) e)[i]!.size = N := by
  obtain ⟨hl, hw, -⟩ := lift_form hk he
  have hil : i < e.words.length := by rw [hl]; exact hi
  have e1 : (liftArrs (wordArrs Data.MWords) e)[i]! =
      posArr nPts (wordArrs Data.MWords) (e.words.getD i []) := by
    rw [liftArrs, getElem!_pos _ _ (by simpa using hil), List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem _ _ hil]
  rw [e1]
  exact ⟨prep_posArr_h (hw _ (by rw [List.getD_eq_getElem _ _ hil]; exact List.getElem_mem hil)),
    posArr_size _ _⟩


theorem lifts_length_list :
    localCert.records.map (fun r => r.lifts.length) = [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0] := by
  have h := local_form_cert
  simp only [localFormOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem recK_lifts_length
    {k : ℕ} (hk : k < 12) :
    (recK k).lifts.length = [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0].getD k 0 := by
  have hk' : k < localCert.records.length := by rw [records_length]; exact hk
  have h := congrArg (fun l => l.getD k 0) lifts_length_list
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk'), List.getElem_map] at h
  rw [← h, recK, List.getD_eq_getElem _ _ hk']

theorem lift_record_cases
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    k = 0 ∨ k = 3 ∨ k = 9 ∨ k = 10 := by
  have hlen := recK_lifts_length hk
  have hne : (recK k).lifts.length ≠ 0 := fun h => by
    rw [List.length_eq_zero_iff] at h
    rw [h] at he
    exact absurd he List.not_mem_nil
  rw [hlen] at hne
  interval_cases k <;> simp only [List.getD_cons_succ, List.getD_cons_zero] at hne <;> omega

end CFSG.Sporadic.ONOddCore
