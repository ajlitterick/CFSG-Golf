module

public import CFSG.Sporadic.Recognition.LyonsAmalgamGlue
public import CFSG.Sporadic.Recognition.LyonsAmalgamGlueModel
public import CFSG.Sporadic.Recognition.LyonsModelStage

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Glue

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Recognition.LyonsSims

@[expose] noncomputable def txG (k : ℕ) : Perm (Fin Ly0.deg) :=
  Ly0.wG Ly0.gens0 (txWords.getD k [])

@[expose] noncomputable def txyBp (j : ℕ) : Perm (Fin Ly0.deg) :=
  wordG (wordLetter Ly0.uG) Ly1080.txyWords[j]!

theorem txWords_length : txWords.length = 4 := rfl


theorem txWords_range : ∀ w ∈ txWords, ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro w hw l hl
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hw
  exact Ly0.decodeWord_mem s l hl

theorem txWords_getD_range {k : ℕ} (hk : k < 4) :
    ∀ l ∈ txWords.getD k [], l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro l hl
  refine txWords_range _ ?_ l hl
  rw [List.getD_eq_getElem _ _ (by rw [txWords_length]; exact hk)]
  exact List.getElem_mem _


theorem Txy0_le_closure1080 (hY : Ly1080.YOK) :
    Ly1080.Txy0 ≤ Subgroup.closure (Ly1080.txyG '' {l | l < 5}) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨T, hT, rfl⟩
  have hT' : T ∈ Ly1080.txyTabs := by simpa using hT
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hT'
  have hsz := (Ly1080.tablesOK_sizes (Ly1080.yCheck_tables hY)).2
  have e : tp Ly1080.deg Ly1080.txyTabs[j] = Ly1080.txyG j := by
    have := Ly1080.tp_txyTab hY (j := j) (by omega)
    rwa [getElem!_pos Ly1080.txyTabs j hj] at this
  have hj5 : j < 5 := by omega
  rw [e]
  exact Subgroup.subset_closure ⟨j, hj5, rfl⟩


theorem wordG_mem_closure {A : Type*} [Group A] (g : ℕ → A) (m : ℕ) {w : List ℤ}
    (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m) :
    wordG (wordLetter g) w ∈ Subgroup.closure (g '' {k | k < m}) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons l w ih =>
    have hl := hw l (List.mem_cons_self ..)
    have hw' : ∀ l' ∈ w, l' ≠ 0 ∧ l'.natAbs ≤ m := fun l' hl' =>
      hw l' (List.mem_cons_of_mem _ hl')
    have e : wordG (wordLetter g) (l :: w) = wordLetter g l * wordG (wordLetter g) w := rfl
    rw [e]
    refine Subgroup.mul_mem _ ?_ (ih hw')
    unfold wordLetter
    split_ifs with hpos
    · exact Subgroup.subset_closure ⟨l.toNat - 1, show l.toNat - 1 < m by omega, rfl⟩
    · exact Subgroup.inv_mem _
        (Subgroup.subset_closure ⟨(-l).toNat - 1, show (-l).toNat - 1 < m by omega, rfl⟩)

theorem UYperm_eq : Ly0.UYperm = Subgroup.closure (Ly0.uG '' {k | k < 4}) := by
  have h : Set.range (fun j : Fin 4 => Ly0.uG j.val) = Ly0.uG '' {k | k < 4} := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.val, j.isLt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  show Subgroup.closure (Set.range (fun j : Fin 4 => Ly0.uG j.val)) = _
  rw [h]

theorem Y0_le_closure1080 (hY : Ly1080.YOK) :
    Ly1080.Y0 ≤ Subgroup.closure (Ly1080.ug '' {k | k < 4}) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨T, hT, rfl⟩
  have hT' : T ∈ Ly1080.uTabs := by simpa using hT
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hT'
  have hsz := (Ly1080.tablesOK_sizes (Ly1080.yCheck_tables hY)).1
  have e : tp Ly1080.deg Ly1080.uTabs[j] = Ly1080.ug j := by
    have := Ly1080.rep_u (Ly1080.yCheck_tables hY) (i := j) (by omega)
    rw [getElem!_pos Ly1080.uTabs j hj] at this
    exact rep_unique (rep_tp (Ly1080.tablesOK_perm (Ly1080.yCheck_tables hY) _
      (by rw [List.mem_append, List.mem_append]; left; left; exact Array.getElem_mem_toList _)).1)
      this
  have hj4 : j < 4 := by omega
  rw [e]
  exact Subgroup.subset_closure ⟨j, hj4, rfl⟩

theorem Tx0_le_closure243 (hT : Ly243.trCheck = true) :
    Ly243.Tx0 ≤ Subgroup.closure (Ly243.gg '' {k | k < 4}) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨T, hT', rfl⟩
  have hT'' : T ∈ Ly243.genTabs.toList.take 4 := by simpa using hT'
  obtain ⟨k, hk, hTk⟩ := List.getElem_of_mem hT''
  have hsz := (Ly243.tablesOK_parts hT).1
  have hk4 : k < 4 := by
    have := hk
    simp only [List.length_take, Array.length_toList] at this
    omega
  have e : tp Ly243.deg T = Ly243.gg k := by
    have h1 := Ly243.rep_gg hT (i := k) (by omega)
    have h2 : T = Ly243.genTabs[k]! := by
      rw [← hTk, getElem!_pos Ly243.genTabs k (by omega)]
      simp
    rw [h2]
    exact rep_unique (rep_tp (Ly243.trTables_perm hT _ (by
      rw [List.mem_append, List.mem_append, List.mem_append]
      left; left; left; rw [getElem!_pos Ly243.genTabs k (by omega)]
      exact Array.getElem_mem_toList _)).1) h1
  rw [e]
  exact Subgroup.subset_closure ⟨k, hk4, rfl⟩


theorem card_Txy0_243 (hT : Ly243.trCheck = true) : Nat.card Ly243.Txy0 = 3888 :=
  (ExactEnum.of_enumOK Ly243.deg_lt (fun g hg => (Ly243.trTables_perm hT g (by
    rw [List.mem_append, List.mem_append, List.mem_append]; left; right; exact hg)).1)
    (Ly243.trCheck_parts hT).2.2.2.2.2.1).1


noncomputable abbrev A30p : Subgroup (Perm (Fin Ly0.deg)) :=
  Subgroup.closure ({Ly0.xG, Ly0.y0G, Ly0.w0G} : Set (Perm (Fin Ly0.deg)))

theorem txG_mem_B0 {k : ℕ} (hk : k < 4) : txG k ∈ Ly0.B0 :=
  Ly0.wG_mem Ly0.B0 Ly0.gens0 2 Ly0.gens0_mem _ (txWords_getD_range hk)

theorem txyBp_mem_B0 (hY : Ly1080.YOK) {j : ℕ} (hj : j < 5) : txyBp j ∈ Ly0.B0 := by
  have : txyBp j ∈ Ly0.UYperm := by
    unfold txyBp
    rw [UYperm_eq]
    exact wordG_mem_closure Ly0.uG 4 fun l' hl' => Ly1080.words_range₄ hY _
      (List.mem_append_right _ (Ly1080.txyWords_get_mem hY hj)) l' hl'
  exact Ly0.UYperm_le_B0 this


theorem A30p_mem {a : Perm (Fin Ly0.deg)} (ha : a ∈ A30p) :
    ∃ h : a ∈ Ly0.B0, (⟨a, h⟩ : Ly0.B0) ∈ Ly0.A30 := by
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨Ly0.xG_mem_B0,
        (Subgroup.subset_closure (Set.mem_insert _ _) : Ly0.xB ∈ Ly0.A30)⟩
    · exact ⟨Ly0.y0G_mem_B0,
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) :
          Ly0.yB ∈ Ly0.A30)⟩
    · exact ⟨Ly0.w0G_mem_B0,
        (Subgroup.subset_closure (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_singleton _))) : Ly0.wB ∈ Ly0.A30)⟩
  | one => exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨hxB, hxA⟩ := ihx
    obtain ⟨hyB, hyA⟩ := ihy
    exact ⟨Subgroup.mul_mem _ hxB hyB, Subgroup.mul_mem _ hxA hyA⟩
  | inv x hx ihx =>
    obtain ⟨hxB, hxA⟩ := ihx
    exact ⟨Subgroup.inv_mem _ hxB, Subgroup.inv_mem _ hxA⟩


theorem Pxp_le_B0 : Subgroup.closure (txG '' {k | k < 4}) ≤ Ly0.B0 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  exact txG_mem_B0 hk

theorem Hb_le_B0 (hY : Ly1080.YOK) :
    Subgroup.closure (txyBp '' {l | l < 5}) ≤ Ly0.B0 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨l, hl, rfl⟩
  exact txyBp_mem_B0 hY hl

theorem txyBp_mem_UYperm (hY : Ly1080.YOK) {j : ℕ} (hj : j < 5) :
    txyBp j ∈ Ly0.UYperm := by
  unfold txyBp
  rw [UYperm_eq]
  exact wordG_mem_closure Ly0.uG 4 fun l' hl' => Ly1080.words_range₄ hY _
    (List.mem_append_right _ (Ly1080.txyWords_get_mem hY hj)) l' hl'


end CFSG.Sporadic.Recognition.LyonsSims.Glue
