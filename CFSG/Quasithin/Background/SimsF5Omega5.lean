module

public import CFSG.Quasithin.Background.SimsF5Defs
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

section Reflections

open Matrix CFSG.Fischer.Classification CFSG.Fischer.Classification.F3


theorem I5Form_single (i : Fin 5) : I5Form (Pi.single i 1) (Pi.single i 1) = 1 := by
  rw [I5Form_apply]
  simp [Pi.single_apply]

theorem I5Form_apply_single (i : Fin 5) (x : Fin 5 → ZMod 3) :
    I5Form x (Pi.single i 1) = x i := by
  rw [I5Form_apply]
  simp [Pi.single_apply]

theorem act_refl_single (i : Fin 5) (x : Fin 5 → ZMod 3) (j : Fin 5) :
    act (refl I5Form (Pi.single i 1)) x j = if j = i then -x j else x j := by
  rw [act_refl (I5Form_single i), I5Form_apply_single]
  by_cases hji : j = i
  · subst hji
    simp
    generalize x j = a
    revert a
    decide
  · simp [Pi.single_apply, hji]

theorem neg_one_eq_prod_refl :
    (-1 : GL (Fin 5) (ZMod 3)) =
      refl I5Form (Pi.single 0 1) * refl I5Form (Pi.single 1 1) * refl I5Form (Pi.single 2 1) *
        refl I5Form (Pi.single 3 1) * refl I5Form (Pi.single 4 1) := by
  refine (gl_ext fun x => ?_).symm
  funext j
  simp only [act_mul, act_neg_one, act_refl_single]
  fin_cases j <;> simp

theorem neg_one_mem_reflGroup_I5 : (-1 : GL (Fin 5) (ZMod 3)) ∈ reflGroup I5Form := by
  rw [neg_one_eq_prod_refl]
  exact mul_mem (mul_mem (mul_mem (mul_mem (refl_mem_reflGroup _) (refl_mem_reflGroup _))
    (refl_mem_reflGroup _)) (refl_mem_reflGroup _)) (refl_mem_reflGroup _)

@[expose] def negOneR : reflGroup I5Form :=
  ⟨-1, neg_one_mem_reflGroup_I5⟩

@[simp]
theorem coe_negOneR : ((negOneR : reflGroup I5Form) : GL (Fin 5) (ZMod 3)) = -1 :=
  rfl


theorem isSimpleGroup_U2_four : IsSimpleGroup (CFSG.Fischer.Classification.Unitary.U2 4) := by
  have : IsSimpleGroup CFSG.GH74.Exceptional.PSp43 :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 3) 2 (by norm_num)
      (Or.inr (Or.inl ⟨by rw [Nat.card_eq_fintype_card, ZMod.card], le_rfl⟩))
  exact CFSG.GH74.Exceptional.psp43EquivU2.symm.isSimpleGroup


end Reflections

section AutPSp43

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher hiding conjAut
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher renaming conjAut → spConjAut

theorem spConjAut_eq_one_of_mem_center {r : ℕ} {K : Type} [Field K] (A : gsp r K)
    (hA : (A : GL (Fin r ⊕ Fin r) K) ∈ Subgroup.center (GL (Fin r ⊕ Fin r) K)) :
    spConjAut r K A = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAut.one_apply]
  have hg : conjSp r K A g = g := Subtype.ext <| by
    rw [coe_conjSp, ← Subgroup.mem_center_iff.1 hA (g : GL (Fin r ⊕ Fin r) K),
      mul_inv_cancel_right]
  have h := conjAut_proj A g
  rw [hg] at h
  exact h

theorem spConjAut_surjective_zmod_three : Function.Surjective (spConjAut 2 (ZMod 3)) := by
  intro α
  obtain ⟨A, σ, hα⟩ := CFSG.RankThree.PartTwo.KFacts.psp4_odd_automorphism_normal_form
    (K := ZMod 3) (by rw [ZMod.ringChar_zmod_n]; norm_num) α
  refine ⟨A, ?_⟩
  rw [hα, Subsingleton.elim σ 1, map_one, mul_one]

theorem card_gsp_two_zmod_three_le : Nat.card (gsp 2 (ZMod 3)) ≤ 2 * 51840 := by
  have h := Subgroup.card_ker_mul_card_range (multiplier 2 (ZMod 3))
  rw [ker_multiplier,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (statedSp_le_gsp (r := 2) (K := ZMod 3))).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two_zmod_three] at h
  have hr : Nat.card (multiplier 2 (ZMod 3)).range ≤ 2 := by
    have := Subgroup.card_le_card_group (multiplier 2 (ZMod 3)).range
    have h2 : Nat.card (ZMod 3)ˣ = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    omega
  rw [← h]
  exact Nat.mul_le_mul_left _ hr

@[expose] def negOneGsp : gsp 2 (ZMod 3) :=
  ⟨-1, statedSp_le_gsp CFSG.GH74.Exceptional.neg_one_mem_statedSp⟩

theorem negOneGsp_ne_one : negOneGsp ≠ 1 := by
  intro h
  have h0 := congrArg (fun g : gsp 2 (ZMod 3) =>
    ((g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3))
      (.inl 0) (.inl 0)) h
  simp [negOneGsp] at h0
  exact absurd h0 (by decide)

theorem negOneGsp_mem_ker : negOneGsp ∈ (spConjAut 2 (ZMod 3)).ker := by
  rw [MonoidHom.mem_ker]
  refine spConjAut_eq_one_of_mem_center _ ?_
  rw [Subgroup.mem_center_iff]
  intro g
  change g * -1 = -1 * g
  rw [mul_neg_one, neg_one_mul]

theorem card_mulAut_PSp43_le : Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) ≤ 51840 := by
  have h1 : Nat.card (spConjAut 2 (ZMod 3)).ker *
      Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) = Nat.card (gsp 2 (ZMod 3)) :=
    Subgroup.card_ker_mul_card_of_surjective spConjAut_surjective_zmod_three
  have h2 : 2 ≤ Nat.card (spConjAut 2 (ZMod 3)).ker := by
    refine (Subgroup.one_lt_card_iff_ne_bot _).2 fun hbot => ?_
    have := negOneGsp_mem_ker
    rw [hbot, Subgroup.mem_bot] at this
    exact negOneGsp_ne_one this
  have h3 := card_gsp_two_zmod_three_le
  have h4 := Nat.mul_le_mul_right (Nat.card (MulAut CFSG.GH74.Exceptional.PSp43)) h2
  omega

theorem card_mulAut_of_mulEquiv_PSp43 {G : Type} [Group G]
    (e : G ≃* CFSG.GH74.Exceptional.PSp43) : Nat.card (MulAut G) ≤ 51840 := by
  rw [Nat.card_congr (MulAut.congr e).toEquiv]
  exact card_mulAut_PSp43_le


end AutPSp43

end

end CFSG.Quasithin.SimsF5
