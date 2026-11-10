module

public import CFSG.ClassicalInvolution.Q3.Q3ZAHeisPres

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups commutatorElement
open Matrix

@[expose] def heisGens : Set Heis :=
  {Heis.center, Heis.vec bE0, Heis.vec bE1, Heis.vec bF0, Heis.vec bF1}

theorem heis_decomp (m : Heis) : m = (⟨m.c, 0⟩ : Heis) * Heis.vec m.v := by
  refine Heis.ext ?_ ?_
  · simp [Heis.mul_def, Heis.vec, form_zero_left]
  · simp [Heis.mul_def, Heis.vec]

theorem heis_closure_center (a : F3) : (⟨a, 0⟩ : Heis) ∈ Subgroup.closure heisGens := by
  rcases eq_zero_or_one_or_neg_one_f3 a with rfl | rfl | rfl
  · rw [show (⟨0, 0⟩ : Heis) = 1 from rfl]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (Or.inl rfl)
  · have h : (⟨-1, 0⟩ : Heis) = Heis.center⁻¹ := by
      refine Heis.ext ?_ ?_ <;> simp [Heis.inv_def, Heis.center]
    rw [h]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl rfl))

theorem heis_closure_vec_smul {b : V4} (hb : Heis.vec b ∈ Subgroup.closure heisGens) (x : F3) :
    Heis.vec (x • b) ∈ Subgroup.closure heisGens := by
  rcases eq_zero_or_one_or_neg_one_f3 x with rfl | rfl | rfl
  · rw [zero_smul, show Heis.vec 0 = 1 from rfl]
    exact Subgroup.one_mem _
  · rwa [one_smul]
  · rw [neg_smul, one_smul, ← vec_inv]
    exact Subgroup.inv_mem _ hb

theorem heis_closure_vec_add {v w : V4} (hv : Heis.vec v ∈ Subgroup.closure heisGens)
    (hw : Heis.vec w ∈ Subgroup.closure heisGens) :
    Heis.vec (v + w) ∈ Subgroup.closure heisGens := by
  have h : Heis.vec (v + w) = (⟨-(2 * form v w), 0⟩ : Heis) * (Heis.vec v * Heis.vec w) := by
    refine Heis.ext ?_ ?_
    · simp [Heis.mul_def, Heis.vec, form_zero_left]
    · simp [Heis.mul_def, Heis.vec]
  rw [h]
  exact Subgroup.mul_mem _ (heis_closure_center _) (Subgroup.mul_mem _ hv hw)

theorem heis_closure_vec (v : V4) : Heis.vec v ∈ Subgroup.closure heisGens := by
  have hb0 : Heis.vec bE0 ∈ Subgroup.closure heisGens :=
    Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hb1 : Heis.vec bE1 ∈ Subgroup.closure heisGens :=
    Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  have hf0 : Heis.vec bF0 ∈ Subgroup.closure heisGens :=
    Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hf1 : Heis.vec bF1 ∈ Subgroup.closure heisGens :=
    Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hv : v = v (Sum.inl 0) • bE0 + v (Sum.inl 1) • bE1 + v (Sum.inr 0) • bF0 +
      v (Sum.inr 1) • bF1 := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp
  rw [hv]
  exact heis_closure_vec_add (heis_closure_vec_add (heis_closure_vec_add
    (heis_closure_vec_smul hb0 _) (heis_closure_vec_smul hb1 _)) (heis_closure_vec_smul hf0 _))
    (heis_closure_vec_smul hf1 _)

theorem heis_closure_eq_top : Subgroup.closure heisGens = ⊤ := by
  rw [eq_top_iff]
  intro m _
  rw [heis_decomp m]
  exact Subgroup.mul_mem _ (heis_closure_center _) (heis_closure_vec _)

@[expose] noncomputable def sp4Gens : Set (StatedSp 2 F3) :=
  {sbU, sbL, longBlock F3 2 1 uSL, longBlock F3 2 1 lSL}

theorem map_SL2_mem_of {H : Type} [Group H] (f : SL(2, F3) →* H) (T : Subgroup H)
    (hU : f uSL ∈ T) (hL : f lSL ∈ T) (g : SL(2, F3)) : f g ∈ T := by
  have hc : ∀ c : F3, f (usl c) ∈ T ∧ f (lsl c) ∈ T := by
    intro c
    rcases eq_zero_or_one_or_neg_one_f3 c with rfl | rfl | rfl
    · rw [usl_zero, lsl_zero, map_one]
      exact ⟨T.one_mem, T.one_mem⟩
    · exact ⟨hU, hL⟩
    · refine ⟨?_, ?_⟩
      · rw [← usl_inv, map_inv]
        exact T.inv_mem hU
      · rw [← lsl_inv, map_inv]
        exact T.inv_mem hL
  have hle : Subgroup.closure (Set.range (CFSG.LieType.Steinberg.sl2Upper : F3 → SL(2, F3)) ∪
      Set.range (CFSG.LieType.Steinberg.sl2Lower : F3 → SL(2, F3))) ≤ T.comap f := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact (hc c).1
    · exact (hc c).2
  exact hle (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 g)

theorem sp4Gens_closure : Subgroup.closure sp4Gens = ⊤ := by
  have hsb : ∀ g : SL(2, F3), sb g ∈ Subgroup.closure sp4Gens := fun g =>
    map_SL2_mem_of sb _ (Subgroup.subset_closure (Or.inl rfl))
      (Subgroup.subset_closure (Or.inr (Or.inl rfl))) g
  have hlb : ∀ g : SL(2, F3), longBlock F3 2 1 g ∈ Subgroup.closure sp4Gens := fun g =>
    map_SL2_mem_of (longBlock F3 2 1) _
      (Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl))))
      (Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))) g
  rw [eq_top_iff, ← shortBlock_sup_longBlock_eq_top F3]
  refine sup_le ?_ ?_
  · rintro _ ⟨g, rfl⟩
    exact hsb g
  · rintro _ ⟨g, rfl⟩
    exact hlb g

section Gen

variable {G : Type} [Group G] {θ : StatedSp 2 F3 →* G} {φ : Heis →* G}


end Gen

theorem heisAct_center (s : StatedSp 2 F3) : heisAct s Heis.center = Heis.center := by
  refine Heis.ext rfl ?_
  show (mat 2 F3 s).mulVec 0 = 0
  exact Matrix.mulVec_zero _


theorem vec_add_eq (v w : V4) :
    Heis.vec (v + w) = (⟨-(2 * form v w), 0⟩ : Heis) * (Heis.vec v * Heis.vec w) := by
  refine Heis.ext ?_ ?_
  · simp [Heis.mul_def, Heis.vec, form_zero_left]
  · simp [Heis.mul_def, Heis.vec]


theorem lb1U_e0 : mat 2 F3 (longBlock F3 2 1 uSL) *ᵥ bE0 = bE0 :=
  lb_mulVec_other 1 uSL (by simp [coords])

theorem lb1U_f0 : mat 2 F3 (longBlock F3 2 1 uSL) *ᵥ bF0 = bF0 :=
  lb_mulVec_other 1 uSL (by simp [coords])

theorem lb1U_e1 : mat 2 F3 (longBlock F3 2 1 uSL) *ᵥ bE1 = bE1 := by
  rw [lb_mulVec_inl 1 uSL]
  simp [uSL]

theorem lb1U_f1 : mat 2 F3 (longBlock F3 2 1 uSL) *ᵥ bF1 = bE1 + bF1 := by
  rw [lb_mulVec_inr 1 uSL]
  simp [uSL]

theorem lb1L_e0 : mat 2 F3 (longBlock F3 2 1 lSL) *ᵥ bE0 = bE0 :=
  lb_mulVec_other 1 lSL (by simp [coords])

theorem lb1L_f0 : mat 2 F3 (longBlock F3 2 1 lSL) *ᵥ bF0 = bF0 :=
  lb_mulVec_other 1 lSL (by simp [coords])

theorem lb1L_e1 : mat 2 F3 (longBlock F3 2 1 lSL) *ᵥ bE1 = bE1 + bF1 := by
  rw [lb_mulVec_inl 1 lSL]
  simp [lSL]

theorem lb1L_f1 : mat 2 F3 (longBlock F3 2 1 lSL) *ᵥ bF1 = bF1 := by
  rw [lb_mulVec_inr 1 lSL]
  simp [lSL]

section Action


end Action

end CFSG.ClassicalInvolution.Q3.Q3ZA
