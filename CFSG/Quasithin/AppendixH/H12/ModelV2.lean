module

public import CFSG.Quasithin.AppendixH.H12.ModelM0
import CFSG.Quasithin.AppendixH.H12.ModelV2T0K

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open
open CFSG.ASVolI.ChH (IsConjPt IsIsoPoint IsExtOf IsIntDirect cenIn ptStab)

private theorem list_two_valid {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    ∀ c ∈ [a, b], c < 4096 := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption


private theorem eq_1465_of_mem_hypPts {r : ℕ} (hr : r ∈ hypPts) (h : ptSub r = ptSub 1465) :
    r = 1465 := by
  have hline : r ∈ lineOf 1465 :=
    (ptSub_eq_iff (by norm_num) (by norm_num) (hypPts_lt r hr)).mp h.symm
  have hcheck : hypPts.all (fun r => !((lineOf 1465).contains r) || (r == 1465)) = true := by
    decide +kernel
  have hc := (List.all_eq_true.mp hcheck) r hr
  rw [List.contains_iff_mem.mpr hline, Bool.not_true, Bool.false_or] at hc
  exact beq_iff_eq.mp hc


theorem ptSub_1465_le_Wsub : ptSub 1465 ≤ Wsub := by
  rw [ptSub, Wsub]
  refine (spanSub_le_iff (list_two_valid (by norm_num) (z12_lt 1465)) Wb_valid).mpr ?_
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact List.contains_iff_mem.mp (by decide +kernel)
  · exact List.contains_iff_mem.mp (by decide +kernel)


theorem ptStab_V2_le_M0 : ptStab glHom G0 (ptSub 1465) ≤ M0 := by
  intro g hg
  rw [mem_ptStab_iff] at hg ⊢
  obtain ⟨hgG, hgfix⟩ := hg
  refine ⟨hgG, ?_⟩
  obtain ⟨b', hb', hb'eq⟩ := planes_closed hgG Wb_mem_planes
  have hmemP : dc 1465 ∈ smulSub g (ptSub 1465) := by
    rw [hgfix]
    exact Subgroup.subset_closure ⟨1465, List.mem_cons_self, rfl⟩
  have hmem : dc 1465 ∈ spanSub b' := by
    rw [← hb'eq]
    exact Subgroup.map_mono (f := (glHom g).toMonoidHom) ptSub_1465_le_Wsub hmemP
  have h1465 : 1465 ∈ spanN b' :=
    (dc_mem_spanSub_iff (planes_valid b' hb') (by norm_num)).mp hmem
  have hb'W : spanSub b' = Wsub := plane_through_1465 hb' (by simp [lineOf]) h1465
  change smulSub g (spanSub Wb) = spanSub Wb
  rw [hb'eq]
  exact hb'W


@[expose] def hyp5 : List ℕ := [1316, 1326, 1365, 1370, 1468]

@[expose] def hyp5Gen (i : ℕ) : List ℕ := [hyp5.getD i 0, mvN z12 (hyp5.getD i 0)]

private theorem hyp5_length : hyp5.length = 5 := by decide

theorem hyp5_sub : ∀ r ∈ hyp5, r ∈ hypPts := by
  have h : hyp5.all (fun r => hypPts.contains r) = true := by decide
  intro r hr
  exact List.contains_iff_mem.mp ((List.all_eq_true.mp h) r hr)

theorem hyp5_ne : ∀ r ∈ hyp5, r ≠ 1465 := by
  have h : hyp5.all (fun r => r != 1465) = true := by decide
  intro r hr
  exact bne_iff_ne.mp ((List.all_eq_true.mp h) r hr)

theorem hyp5Gen_valid : ∀ i < 5, ∀ c ∈ hyp5Gen i, c < 4096 := by
  have h : (List.range 5).all (fun i => (hyp5Gen i).all (fun c => decide (c < 4096))) = true := by
    decide +kernel
  intro i hi c hc
  exact of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp h) i (List.mem_range.mpr hi))) c hc)

theorem hyp5Gen_inj : ∀ i < 5, ∀ j < 5, spanSub (hyp5Gen i) = spanSub (hyp5Gen j) → i = j := by
  have hnd : ((List.range 5).map (fun i => spanMask (hyp5Gen i))).Nodup := by
    decide +kernel
  intro i hi j hj hij
  have hm : spanMask (hyp5Gen i) = spanMask (hyp5Gen j) :=
    (spanMask_eq_iff (hyp5Gen_valid i hi) (hyp5Gen_valid j hj)).mpr hij
  exact List.inj_on_of_nodup_map hnd (List.mem_range.mpr hi) (List.mem_range.mpr hj) hm

theorem vecStab_1465_le_M0 : vecStab 1465 ≤ M0 := by
  intro x hx
  obtain ⟨hxG, hxfix⟩ := (mem_vecStab_iff (by norm_num) x).mp hx
  have hmem : x ∈ ptStab glHom G0 (ptSub 1465) := by
    rw [mem_ptStab_iff]
    exact ⟨hxG, by rw [smulSub_ptSub hxG (by norm_num), hxfix]⟩
  exact ptStab_V2_le_M0 hmem


theorem exists_p2 : ∃ π : ↥(vecStab 1465) →* Equiv.Perm (Fin 5),
    ∀ (g : ↥(vecStab 1465)) (i : Fin 5),
      smulSub (g : Γ12) (spanSub (hyp5Gen i)) = spanSub (hyp5Gen (π g i)) := by
  refine exists_actHom (vecStab 1465) hyp5Gen hyp5Gen_inj ?_
  intro g hg i hi
  set r := hyp5.getD i 0 with hrdef
  have hr5 : r ∈ hyp5 := by
    rw [hrdef]
    rw [List.getD_eq_getElem _ _ (by simpa [hyp5_length] using hi)]
    exact List.getElem_mem _
  have hrhyp : r ∈ hypPts := hyp5_sub r hr5
  have hrlt : r < 4096 := hypPts_lt r hrhyp
  have hgM : g ∈ M0 := vecStab_1465_le_M0 hg
  obtain ⟨r', hr', hconj⟩ := exists_hyp_image hgM hrhyp
  have hr'ne : r' ≠ 1465 := by
    intro heq
    have hgvec : gmv g 1465 = 1465 := (mem_vecStab_iff (by norm_num) g).mp hg |>.2
    have hfix : smulSub g (ptSub 1465) = ptSub 1465 := by
      rw [smulSub_ptSub (vecStab_le_G0 1465 hg) (by norm_num), hgvec]
    have hpr : ptSub r = ptSub 1465 := by
      have h1 : smulSub g (ptSub r) = smulSub g (ptSub 1465) := by
        rw [hconj, heq, hfix]
      have h2 := congrArg (smulSub g⁻¹) h1
      rwa [← smulSub_mul, inv_mul_cancel, smulSub_one, ← smulSub_mul, inv_mul_cancel,
        smulSub_one] at h2
    exact hyp5_ne r hr5 (eq_1465_of_mem_hypPts hrhyp hpr)
  have hr'5 : r' ∈ hyp5 := by
    have hcheck : hypPts.all (fun r => (r == 1465) || hyp5.contains r) = true := by
      decide +kernel
    have hh := (List.all_eq_true.mp hcheck) r' hr'
    rw [Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact absurd (beq_iff_eq.mp hh) hr'ne
    · exact List.contains_iff_mem.mp hh
  obtain ⟨j, hj, hjget⟩ := List.mem_iff_getElem.mp hr'5
  have hj5 : j < 5 := by rwa [hyp5_length] at hj
  refine ⟨j, hj5, ?_⟩
  have hspan_i : spanSub (hyp5Gen i) = ptSub r := by
    simp only [hyp5Gen, ← hrdef]
    rfl
  have hspan_j : spanSub (hyp5Gen j) = ptSub r' := by
    have hg' : hyp5.getD j 0 = r' := (List.getD_eq_getElem _ _ hj).trans hjget
    simp only [hyp5Gen, hg']
    rfl
  calc smulSub g (spanSub (hyp5Gen i)) = smulSub g (ptSub r) := by rw [hspan_i]
    _ = ptSub r' := hconj
    _ = spanSub (hyp5Gen j) := hspan_j.symm

noncomputable def p2 : ↥(vecStab 1465) →* Equiv.Perm (Fin 5) := Classical.choose exists_p2


@[expose] def x60 : List (List ℕ) := [
    [], [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1],
    [0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0],
    [0, 1, 0, 1, 1, 1, 0], [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1],
    [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0],
    [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
    [1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1],
    [0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1],
    [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
    [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0],
    [0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0],
    [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1]]


end CFSG.Quasithin.AppendixH.H12.Model
