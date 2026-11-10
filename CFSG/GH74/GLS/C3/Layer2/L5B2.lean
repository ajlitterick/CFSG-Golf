module

public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2Inputs
public import Certificates.Certificate5049

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

structure SPair (α : Amb 5 → Amb 5) (u : Amb 5) : Prop where
  maps : ∀ t ∈ T5, α t ∈ T5
  mul : ∀ s ∈ T5, ∀ t ∈ T5, α (s * t) = α s * α t
  surj : ∀ t ∈ T5, ∃ s ∈ T5, α s = t
  P_Q : ∀ p ∈ Pm, α p ∈ Qm
  Q_P : ∀ q ∈ Qm, α q ∈ Pm
  u_mem : u ∈ T5
  sq : ∀ t ∈ T5, α (α t) = u * t * u⁻¹
  fix : α u = u
  moves : α f1 ≠ f1

theorem SPair.one
    {α : Amb 5 → Amb 5} {u : Amb 5} (h : SPair α u) : α 1 = 1 := by
  have h1 := h.mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h1
  exact mul_left_cancel (a := α 1) (by rw [mul_one]; exact h1.symm)

theorem Wl_cover_chk :
    allT5.all (fun t => Wl.any fun w => decide (evalW gT w = t)) = true :=
  Certificates.certificate5049.1

theorem Wl_cover
    {t : Amb 5} (ht : t ∈ T5) : ∃ w ∈ Wl, evalW gT w = t := by
  have h := Wl_cover_chk
  simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  exact h t (mem_allT5.2 ht)

theorem Rels_chk :
    Rels.all (fun r => decide (evalW gT r = 1)) = true :=
  Certificates.certificate5049.2.1

theorem Rels_eval : ∀ r ∈ Rels, evalW gT r = 1 := by
  have h := Rels_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem gT_mem_chk :
    T5b (gT 0) = true ∧ T5b (gT 1) = true ∧ T5b (gT 2) = true :=
  Certificates.certificate5049.2.2.1

theorem gT_mem (i : Fin 3) : gT i ∈ T5 := by
  obtain ⟨h0, h1, h2⟩ := gT_mem_chk
  fin_cases i
  · exact mem_T5_of_b h0
  · exact mem_T5_of_b h1
  · exact mem_T5_of_b h2

theorem foldl_hom {M : Type*} [Monoid M] {f : Amb 5 → M}
    (hf : ∀ s ∈ T5, ∀ t ∈ T5, f (s * t) = f s * f t) :
    ∀ (w : List (Fin 3)) (a : Amb 5), a ∈ T5 →
      f (w.foldl (fun a i => a * gT i) a) = w.foldl (fun m i => m * f (gT i)) (f a)
  | [], _, _ => rfl
  | i :: w, a, ha => by
      simp only [List.foldl_cons]
      rw [foldl_hom hf w (a * gT i) (mul_mem ha (gT_mem i)), hf a ha (gT i) (gT_mem i)]

theorem eq_of_gens {M : Type*} [Monoid M] {f f' : Amb 5 → M}
    (hf : ∀ s ∈ T5, ∀ t ∈ T5, f (s * t) = f s * f t)
    (hf' : ∀ s ∈ T5, ∀ t ∈ T5, f' (s * t) = f' s * f' t) (h1 : f 1 = f' 1)
    (h : ∀ i, f (gT i) = f' (gT i)) {t : Amb 5} (ht : t ∈ T5) : f t = f' t := by
  obtain ⟨w, -, rfl⟩ := Wl_cover ht
  unfold evalW
  rw [foldl_hom hf w 1 (one_mem _), foldl_hom hf' w 1 (one_mem _), h1]
  simp only [h]

theorem evalW_hom
    {α : Amb 5 → Amb 5} (hα : ∀ s ∈ T5, ∀ t ∈ T5, α (s * t) = α s * α t)
    (h1 : α 1 = 1) (w : List (Fin 3)) :
    α (evalW gT w) = evalW (fun i => α (gT i)) w := by
  unfold evalW
  rw [foldl_hom hα w 1 (one_mem _), h1]

theorem main27_true : main27 = true :=
  Certificates.certificate5049.2.2.2.1

theorem xChk_of_SPair
    {α : Amb 5 → Amb 5} {u : Amb 5} (h : SPair α u) :
    xChk (fun i => α (gT i)) = true := by
  have hev := evalW_hom h.mul h.one
  simp only [xChk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, imp_eq_true,
    List.any_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    rw [← hev, Rels_eval r hr, h.one]
  · intro w _
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hp
      rw [← hev]
      exact h.P_Q _ (mem_Pm.2 hp)
    · intro hq
      rw [← hev]
      exact h.Q_P _ (mem_Qm.2 hq)
    · intro hf
      rw [← hev, hf]
      exact h.moves
  · intro t ht
    obtain ⟨s, hs, e⟩ := h.surj t (mem_allT5.1 ht)
    obtain ⟨w, hw, rfl⟩ := Wl_cover hs
    exact ⟨_, List.mem_map.2 ⟨w, hw, rfl⟩, by rw [← hev, e]⟩

theorem uChk_of_SPair
    {α : Amb 5 → Amb 5} {u : Amb 5} (h : SPair α u) {w : List (Fin 3)}
    (hw : evalW gT w = u) : uChk (fun i => α (gT i)) w = true := by
  have hev := evalW_hom h.mul h.one
  simp only [uChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true]
  refine ⟨?_, ?_⟩
  · rw [← hev, hw]
    exact h.fix
  · intro i _
    obtain ⟨w', hw', e⟩ := Wl_cover (h.maps _ (gT_mem i))
    refine ⟨w', hw', e, ?_⟩
    rw [← hev, e, hw]
    exact h.sq _ (gT_mem i)

theorem e2_mem_Pm : e2 ∈ Pm := by simp [mem_Pm, Pml]

theorem classify_27_id
    {α : Amb 5 → Amb 5} {u : Amb 5} (h : SPair α u) (hu : u ∈ Rm) :
    ∃ t₀ ∈ T5, (∀ t ∈ T5, emb 5 (α t) =
        emb 5 t₀ * a0perm 5 * emb 5 t * (a0perm 5)⁻¹ * (emb 5 t₀)⁻¹) ∧
      emb 5 u = emb 5 t₀ * a0perm 5 * emb 5 t₀ * a0perm 5 := by
  have hxa : α f2 ∈ Pml := mem_Pm.1 (h.Q_P f2 f2_mem_Qm)
  have hxc : α e2 ∈ Qml := mem_Qm.1 (h.P_Q e2 e2_mem_Pm)
  have hxb : α (swap 2 3, swap 2 3) ∈ allT5 := mem_allT5.2 (h.maps _ (gT_mem 1))
  have hg : (fun i => α (gT i)) = ![α f2, α (swap 2 3, swap 2 3), α e2] := by
    funext i
    fin_cases i <;> rfl
  have hm := main27_true
  simp only [main27, List.all_eq_true] at hm
  have hc : candChk (fun i => α (gT i)) = true := by
    rw [hg]
    exact hm _ hxa _ hxc _ hxb
  obtain ⟨w, hw, hwu⟩ := Wl_cover h.u_mem
  have hX := xChk_of_SPair h
  have hU := uChk_of_SPair h hwu
  have hc2 : (Wl.all fun w => !(decide (evalW gT w ∈ Rml)) || !(uChk (fun i => α (gT i)) w) ||
      allT5.any fun t₀ => gensRel (fun i => α (gT i)) (evalW gT w) t₀) = true := by
    unfold candChk at hc
    rw [hX] at hc
    simpa only [Bool.not_true, Bool.false_or] using hc
  have h3 := List.all_eq_true.1 hc2 w hw
  rw [hwu, decide_eq_true (mem_Rm.1 hu), hU] at h3
  simp only [Bool.not_true, Bool.false_or] at h3
  obtain ⟨t₀, ht₀, hr⟩ := List.any_eq_true.1 h3
  simp only [gensRel, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr
  refine ⟨t₀, mem_allT5.1 ht₀, fun t ht => ?_, hr.1⟩
  refine eq_of_gens (f := fun t => emb 5 (α t))
    (f' := fun t => emb 5 t₀ * a0perm 5 * emb 5 t * (a0perm 5)⁻¹ * (emb 5 t₀)⁻¹) ?_ ?_ ?_ ?_ ht
  · intro s hs t ht
    simp only [h.mul s hs t ht, map_mul]
  · intro s hs t ht
    simp only [map_mul]
    group
  · simp only [h.one, map_one, mul_one]
    group
  · intro i
    exact hr.2 i (List.mem_finRange i)

theorem nm_id_chk :
    allT5.all (fun t => imp (decide (t * t = 1)) (imp (decide (t ≠ 1))
    (decide (nmE t = 8 ↔ (t ∈ Rml ∧ t ∉ Pml ∧ t ∉ Qml))))) = true :=
  Certificates.certificate5049.2.2.2.2.1

theorem nm_id :
    ∀ t ∈ T5, t * t = 1 → t ≠ 1 → (nmE t = 8 ↔ (t ∈ Rm ∧ t ∉ Pm ∧ t ∉ Qm)) := by
  have h := nm_id_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact fun t ht h1 h2 => h t (mem_allT5.2 ht) h1 h2


end CFSG.GH74.GLS.C3.Layer2.L5
