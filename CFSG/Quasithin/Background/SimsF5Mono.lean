module

public import CFSG.Quasithin.Background.SimsF5Form
public import CFSG.Quasithin.Background.SimsF5Klein
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix CFSG.Open
open scoped Pointwise

theorem mono_xvec_apply (i k : Fin 6) : xvec i k = if k = i then 1 else 0 := by
  simp [xvec, Pi.single_apply]

theorem mono_xvec_ne_zero (i : Fin 6) : xvec i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [mono_xvec_apply] at this


theorem mono_qV_xvec (i : Fin 6) : qV (xvec i) = if i = 5 then -1 else 1 := by
  fin_cases i <;> decide

theorem mono_qV_smul (c : ZMod 3) (v : V6) : qV (c • v) = c ^ 2 * qV v := by
  simp only [qV, Pi.smul_apply, smul_eq_mul]; ring


theorem mono_mulVec_inj (g : GL6) {u v : V6}
    (h : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ u = (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) :
    u = v := by
  have h2 := congrArg (fun w => ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w) h
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
  exact h2


theorem mono_mulVec_inv (g : GL6) (v : V6) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      (((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem mono_eJ_val (J : Finset (Fin 6)) :
    ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = Matrix.diagonal (eJd J) := rfl

theorem mono_eJd_apply (J : Finset (Fin 6)) (i : Fin 6) :
    eJd J i = if i ∈ J then -1 else 1 := rfl

theorem mono_eJ_mulVec (J : Finset (Fin 6)) (x : V6) :
    ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x = fun k => eJd J k * x k := by
  funext k
  rw [mono_eJ_val, Matrix.mulVec_diagonal]

theorem mono_eJ_mulVec_xvec (J : Finset (Fin 6)) (i : Fin 6) :
    ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = eJd J i • xvec i := by
  rw [mono_eJ_mulVec]
  funext k
  by_cases hk : k = i
  · subst hk; simp [mono_xvec_apply]
  · simp [mono_xvec_apply, hk]

theorem mono_eJd_symmDiff (J K : Finset (Fin 6)) (i : Fin 6) :
    eJd (symmDiff J K) i = eJd J i * eJd K i := by
  simp only [mono_eJd_apply]
  by_cases h1 : i ∈ J <;> by_cases h2 : i ∈ K <;> simp [Finset.mem_symmDiff, h1, h2] <;> decide

theorem mono_eJ_mul (J K : Finset (Fin 6)) : eJ J * eJ K = eJ (symmDiff J K) := by
  apply Units.ext
  show Matrix.diagonal (eJd J) * Matrix.diagonal (eJd K) = Matrix.diagonal (eJd (symmDiff J K))
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mono_eJd_symmDiff]

theorem mono_eJ_empty : eJ ∅ = 1 := by
  apply Units.ext
  show Matrix.diagonal (eJd ∅) = 1
  rw [← Matrix.diagonal_one]
  congr 1

theorem mono_eJ_mul_self (J : Finset (Fin 6)) : eJ J * eJ J = 1 := by
  rw [mono_eJ_mul, symmDiff_self, Finset.bot_eq_empty, mono_eJ_empty]


@[expose] def monoReflX (a : Fin 6) : ReflVec := ⟨xvec a, qV_xvec_ne_zero a⟩

theorem mono_reflOf_reflX (a : Fin 6) : reflOf (monoReflX a) = eJ {a} := by
  apply Units.ext
  apply mat_eq_of_mulVec_eq
  intro x
  rw [mono_eJ_mulVec]
  show (refl6 (xvec a) (qV_xvec_ne_zero a) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x = _
  rw [refl6_xvec_mulVec]
  funext k
  by_cases hk : k = a
  · subst hk; simp [mono_eJd_apply]
  · simp [mono_eJd_apply, hk, Function.update_apply]

theorem mono_exists_list (J : Finset (Fin 6)) :
    ∃ l : List ReflVec, (l.map reflOf).prod = eJ J ∧ l.length = J.card ∧
      l.countP (fun v => qV v.1 = -1) = if (5 : Fin 6) ∈ J then 1 else 0 := by
  induction J using Finset.induction_on with
  | empty => exact ⟨[], by simp [mono_eJ_empty], by simp, by simp⟩
  | insert a J ha ih =>
    obtain ⟨l, hl, hlen, hcnt⟩ := ih
    refine ⟨monoReflX a :: l, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, hl, mono_reflOf_reflX, mono_eJ_mul]
      congr 1
      ext i
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      by_cases hi : i = a
      · subst hi; simp [ha]
      · simp [hi]
    · rw [List.length_cons, hlen, Finset.card_insert_of_notMem ha]
    · rw [List.countP_cons, hcnt]
      have hq : qV (monoReflX a).1 = -1 ↔ a = 5 := by
        rw [show (monoReflX a).1 = xvec a from rfl, mono_qV_xvec]
        by_cases h : a = 5 <;> simp [h] <;> decide
      by_cases h5 : a = 5
      · subst h5; simp [monoReflX, mono_qV_xvec, ha]
      · simp [hq, h5, Finset.mem_insert, Ne.symm h5]

theorem mono_eJ_mem_MDot_iff (J : Finset (Fin 6)) :
    eJ J ∈ MDot ↔ Even J.card ∧ (5 : Fin 6) ∉ J := by
  obtain ⟨l, hl, hlen, hcnt⟩ := mono_exists_list J
  rw [← hl, prod_refl_mem_MDot_iff, hlen, hcnt]
  by_cases h : (5 : Fin 6) ∈ J <;> simp [h]

@[expose] def monoDiag : Subgroup GL6 where
  carrier := {g | ∃ J : Finset (Fin 6), g = eJ J}
  mul_mem' := by
    rintro _ _ ⟨J, rfl⟩ ⟨K, rfl⟩
    exact ⟨_, mono_eJ_mul J K⟩
  one_mem' := ⟨∅, mono_eJ_empty.symm⟩
  inv_mem' := by
    rintro _ ⟨J, rfl⟩
    exact ⟨J, inv_eq_of_mul_eq_one_right (mono_eJ_mul_self J)⟩

theorem mono_Qset_eq :
    {g : GL6 | ∃ J : Finset (Fin 6), J ⊆ Iset ∧ Even J.card ∧ g = eJ J} =
      ((MDot ⊓ monoDiag : Subgroup GL6) : Set GL6) := by
  ext g
  constructor
  · rintro ⟨J, hJ, hev, rfl⟩
    refine ⟨(mono_eJ_mem_MDot_iff J).2 ⟨hev, fun h5 => ?_⟩, ⟨J, rfl⟩⟩
    have := hJ h5
    revert this
    decide
  · rintro ⟨hM, J, rfl⟩
    obtain ⟨hev, h5⟩ := (mono_eJ_mem_MDot_iff J).1 hM
    refine ⟨J, fun i hi => ?_, hev, rfl⟩
    have hne : i ≠ 5 := fun h => h5 (h ▸ hi)
    have : ∀ i : Fin 6, i ≠ 5 → i ∈ Iset := by decide
    exact this i hne

theorem mono_Q2Dot_eq : Q2Dot = MDot ⊓ monoDiag := by
  unfold Q2Dot
  rw [mono_Qset_eq]
  exact Subgroup.closure_eq _


theorem mono_mem_Q2Dot_iff (g : GL6) :
    g ∈ Q2Dot ↔ g ∈ MDot ∧ ∃ J : Finset (Fin 6), g = eJ J := by
  rw [mono_Q2Dot_eq, Subgroup.mem_inf]
  rfl

theorem mono_Q2Dot_elim {g : GL6} (hg : g ∈ Q2Dot) : ∃ J : Finset (Fin 6), g = eJ J :=
  ((mono_mem_Q2Dot_iff g).1 hg).2

theorem mono_Q2Dot_le_MDot : Q2Dot ≤ MDot := by
  rw [mono_Q2Dot_eq]
  exact inf_le_left


theorem mono_smul_spn (g : GL6) (v : V6) : g • spn {v} = spn {g • v} := by
  unfold spn
  rw [Units.smul_def, Submodule.smul_span, Set.smul_set_singleton]
  rfl


theorem mono_line_map {g : GL6} (hg : g ∈ MulAction.stabilizer GL6 Lambda) (i : Fin 6) :
    ∃ j : Fin 6, ∃ c : ZMod 3, c ≠ 0 ∧
      (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = c • xvec j := by
  have h1 : g • spn {xvec i} ∈ g • Lambda := Set.smul_mem_smul_set ⟨i, rfl⟩
  rw [MulAction.mem_stabilizer_iff.1 hg] at h1
  obtain ⟨j, hj⟩ := h1
  rw [mono_smul_spn] at hj
  have hmem : g • xvec i ∈ spn {xvec j} := by
    rw [← hj]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  refine ⟨j, c, ?_, hc.symm⟩
  rintro rfl
  rw [zero_smul] at hc
  have h0 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i =
      (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ 0 := by
    rw [Matrix.mulVec_zero]
    exact hc.symm
  exact mono_xvec_ne_zero i (mono_mulVec_inj g h0)

theorem mono_conj_diag {g : GL6} (hg : g ∈ MulAction.stabilizer GL6 Lambda) {d : GL6}
    (hd : ∀ j, ∃ e : ZMod 3,
      (d : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec j = e • xvec j) (i : Fin 6) :
    ∃ e : ZMod 3, ((g * d * g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i =
      e • xvec i := by
  obtain ⟨j, c, hc, hgi⟩ := mono_line_map (inv_mem hg) i
  obtain ⟨e, he⟩ := hd j
  refine ⟨e, ?_⟩
  have h1 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec j = c⁻¹ • xvec i := by
    have := mono_mulVec_inv g (xvec i)
    rw [hgi, Matrix.mulVec_smul] at this
    rw [← this, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgi]
  simp only [Matrix.mulVec_smul, he, h1, smul_smul]
  congr 1
  rw [mul_right_comm, mul_inv_cancel₀ hc, one_mul]

theorem mono_eq_eJ_of_diag {g : GL6} (hg : g ∈ OVq)
    (h : ∀ i, ∃ c : ZMod 3, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = c • xvec i) :
    ∃ J : Finset (Fin 6), g = eJ J := by
  choose c hc using h
  have hc1 : ∀ i, c i = 1 ∨ c i = -1 := by
    intro i
    have h1 := qV_mulVec_of_mem_OVq hg (xvec i)
    rw [hc i, mono_qV_smul] at h1
    have hq := qV_xvec_ne_zero i
    have h2 : c i ^ 2 = 1 := mul_right_cancel₀ hq (h1.trans (one_mul _).symm)
    have key : ∀ a : ZMod 3, a ^ 2 = 1 → a = 1 ∨ a = -1 := by decide
    exact key _ h2
  refine ⟨Finset.univ.filter (fun i => c i = -1), ?_⟩
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  show _ *ᵥ xvec i = _ *ᵥ xvec i
  rw [hc i, mono_eJ_mulVec_xvec]
  congr 1
  rw [mono_eJd_apply]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hc1 i with h | h
  · rw [if_neg (by rw [h]; decide), h]
  · rw [if_pos h, h]


theorem mono_conj_mem_Q2Dot {g : GL6} (hg : g ∈ M2Dot) {q : GL6} (hq : q ∈ Q2Dot) :
    g * q * g⁻¹ ∈ Q2Dot := by
  rw [mono_mem_Q2Dot_iff]
  have hqM : q ∈ MDot := mono_Q2Dot_le_MDot hq
  refine ⟨MDot.mul_mem (MDot.mul_mem hg.1 hqM) (MDot.inv_mem hg.1), ?_⟩
  refine mono_eq_eJ_of_diag (MDot_le_OVq (MDot.mul_mem (MDot.mul_mem hg.1 hqM)
    (MDot.inv_mem hg.1))) fun i => mono_conj_diag hg.2 ?_ i
  obtain ⟨J, rfl⟩ := mono_Q2Dot_elim hq
  exact fun j => ⟨eJd J j, mono_eJ_mulVec_xvec J j⟩

theorem Q2Dot_normal : (Q2Dot.subgroupOf M2Dot).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using mono_conj_mem_Q2Dot g.2 hn


end

end CFSG.Quasithin.SimsF5
