module

public import CFSG.Sporadic.SuzOddCore.Perms
public import CFSG.Sporadic.SuzOddCore.RelabelCheck
public import CFSG.Sporadic.Suz.Simple

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th

theorem perm_apply_inv' {α : Type*} (σ : Equiv.Perm α) (x : α) : σ (σ⁻¹ x) = x := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

theorem perm_inv_apply' {α : Type*} (σ : Equiv.Perm α) (x : α) : σ⁻¹ (σ x) = x := by
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

theorem perm_conj_apply' {α : Type*} (τ σ : Equiv.Perm α) (x : α) :
    (MulAut.conj τ σ) x = τ (σ (τ⁻¹ x)) := by
  rw [MulAut.conj_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

@[expose] def relabelPerm : Equiv.Perm (Fin 22880) := permC 22880 relabelArr

theorem rep_relabelPerm :
    CFSG.Monster.B.Co2.Rep 22880 relabelArr relabelPerm :=
  (rep_permC (Bool.and_eq_true_iff.1 arrays_check.2.2.2.2.2.2.2.2.2.2.2.1).2).1

theorem relabel_facts (i : ℕ) (hi : i < 22880) :
    relabelArr[Native.ap CFSG.Sporadic.Suz.orb.alpha i]! = (certArr 0)[relabelArr[i]!]! ∧
      relabelArr[Native.ap CFSG.Sporadic.Suz.orb.beta i]! = (certArr 1)[relabelArr[i]!]! := by
  have h := relabel_check
  simp only [relabelOK, Bool.and_eq_true, beq_iff_eq] at h
  have := allLt_spec h.2 hi
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this

@[expose] def rhoJ : CFSG.Sporadic.Suz.J →* Equiv.Perm (Fin 22880) :=
  MulAction.toPermHom CFSG.Sporadic.Suz.J (Fin 22880)

theorem rhoJ_apply
    (g : CFSG.Sporadic.Suz.J) (x : Fin 22880) : rhoJ g x = g • x := by
  rw [rhoJ, MulAction.toPermHom_apply, MulAction.toPerm_apply]

theorem rhoJ_injective : Function.Injective rhoJ := by
  intro g h hgh
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin 22880)
  intro x
  rw [← rhoJ_apply, ← rhoJ_apply, hgh]

@[expose] def psiJ : CFSG.Sporadic.Suz.J →* Equiv.Perm (Fin 22880) :=
  (MulAut.conj relabelPerm).toMonoidHom.comp rhoJ

theorem psiJ_apply (g : CFSG.Sporadic.Suz.J) (x : Fin 22880) :
    psiJ g x = relabelPerm (g • relabelPerm⁻¹ x) := by
  rw [psiJ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, perm_conj_apply', rhoJ_apply]

theorem psiJ_injective : Function.Injective psiJ :=
  (MulAut.conj relabelPerm).injective.comp rhoJ_injective

theorem relabel_smul
    (g : CFSG.Sporadic.Suz.J) (T : Native.Table) (t : Array ℕ)
    (σ : Equiv.Perm (Fin 22880)) (hT : Rep 22880 T g) (ht : CFSG.Monster.B.Co2.Rep 22880 t σ)
    (h : ∀ i < 22880, relabelArr[Native.ap T i]! = t[relabelArr[i]!]!) :
    psiJ g = σ := by
  ext x
  rw [psiJ_apply]
  set y := relabelPerm⁻¹ x with hy
  have hx : x = relabelPerm y := by rw [hy, perm_apply_inv']
  rw [hx]
  have e := h y.val y.isLt
  rw [hT y.val y.isLt, idx_of_lt g y.isLt, Fin.eta, rep_relabelPerm (g • y), rep_relabelPerm y,
    ht (relabelPerm y)] at e
  exact congrArg Fin.val (Fin.ext e)

theorem psiJ_a :
    psiJ CFSG.Sporadic.Suz.a = suzA0 :=
  relabel_smul _ _ _ _ CFSG.Sporadic.Suz.rep_alpha rep_suzA0 fun i hi => (relabel_facts i hi).1

theorem psiJ_b :
    psiJ CFSG.Sporadic.Suz.b = suzA1 :=
  relabel_smul _ _ _ _ CFSG.Sporadic.Suz.rep_beta rep_suzA1 fun i hi => (relabel_facts i hi).2

theorem psiJ_range :
    psiJ.range = suzP := by
  rw [MonoidHom.range_eq_map, ← CFSG.Sporadic.Suz.closure_ab, MonoidHom.map_closure, suzP]
  congr 1
  rw [Set.image_insert_eq, Set.image_singleton, psiJ_a, psiJ_b]

@[expose] def suzJEquivP :
    CFSG.Sporadic.Suz.J ≃* suzP :=
  (MonoidHom.ofInjective psiJ_injective).trans (MulEquiv.subgroupCongr psiJ_range)

theorem suzJEquivP_apply
    (g : CFSG.Sporadic.Suz.J) :
    ((suzJEquivP g : suzP) : Equiv.Perm (Fin 22880)) = psiJ g := by
  rw [suzJEquivP, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

@[expose] def suzA0P : suzP := ⟨suzA0, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] def suzA1P : suzP :=
  ⟨suzA1, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

@[expose] def suzSeedEquiv :
    Blueprint.NativeSporadic.Suz ≃* CFSG.Sporadic.Suz.J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 3 64 (by norm_num) CFSG.Sporadic.Suz.mA
    CFSG.Sporadic.Suz.mB (CFSG.Sporadic.Suz.det_mA_ne_zero CFSG.Sporadic.Suz.matrixFacts)
    (CFSG.Sporadic.Suz.det_mB_ne_zero CFSG.Sporadic.Suz.matrixFacts)


@[expose] def suzEquivP :

    Blueprint.NativeSporadic.Suz ≃* suzP := suzSeedEquiv.trans suzJEquivP


theorem suzP_card :
    Nat.card suzP = 448345497600 := by
  rw [← Nat.card_congr suzJEquivP.toEquiv, CFSG.Sporadic.Suz.card_J]

theorem suzP_isSimpleGroup :
    IsSimpleGroup suzP :=
  @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Suz.isSimpleGroup_J suzJEquivP.symm

theorem suzP_isPreprimitive :
    MulAction.IsPreprimitive suzP (Fin 22880) := by
  have hJ := CFSG.Sporadic.Suz.isPreprimitive
  have key : ∀ (g : CFSG.Sporadic.Suz.J) (x : Fin 22880),
      (suzJEquivP g : suzP) • relabelPerm x = relabelPerm (g • x) := by
    intro g x
    rw [Subgroup.smul_def, Equiv.Perm.smul_def, suzJEquivP_apply, psiJ_apply, perm_inv_apply']
  let f : Fin 22880 →ₑ[(suzJEquivP : CFSG.Sporadic.Suz.J → suzP)] Fin 22880 :=
    { toFun := fun x => relabelPerm x
      map_smul' := fun g x => (key g x).symm }
  have hf : Function.Surjective f := fun y => ⟨relabelPerm⁻¹ y, perm_apply_inv' relabelPerm y⟩
  exact MulAction.IsPreprimitive.of_surjective hf

end CFSG.Sporadic.SuzOddCore
