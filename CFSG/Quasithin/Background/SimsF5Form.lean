module

public import CFSG.Quasithin.Background.SimsF5Defs
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

@[expose] def QV : QuadraticForm (ZMod 3) (Fin 6 → ZMod 3) :=
  QuadraticMap.weightedSumSquares (ZMod 3) (![1, 1, 1, 1, 1, -1] : Fin 6 → ZMod 3)

theorem coe_QV : ⇑QV = qV := by
  funext v
  simp only [QV, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_six, qV]
  simp
  ring

theorem polar_QV (x y : V6) : QuadraticMap.polar QV x y = bil x y := by
  rw [coe_QV]
  rfl

local instance : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)

theorem QV_nondeg : (QuadraticMap.polarBilin QV).Nondegenerate := by
  refine QuadraticMap.nondegenerate_polar_iff.mpr ?_
  refine QuadraticMap.nondegenerate_weightedSumSquares fun i => isRegular_iff_ne_zero.mpr ?_
  fin_cases i <;> decide

@[expose] def hp1 : HypPair QV where
  e := ![0, 0, 0, 0, 1, 1]
  f := ![0, 0, 0, 0, 1, 2]
  Q_e := by rw [coe_QV]; decide
  Q_f := by rw [coe_QV]; decide
  polar_ef := by rw [polar_QV]; decide

@[expose] def hp2 : HypPair QV where
  e := ![0, 1, 1, 1, 0, 0]
  f := ![0, 1, 2, 2, 0, 0]
  Q_e := by rw [coe_QV]; decide
  Q_f := by rw [coe_QV]; decide
  polar_ef := by rw [polar_QV]; decide

@[expose] def hp3 : HypPair QV where
  e := ![1, 0, 1, 2, 0, 0]
  f := ![1, 0, 2, 1, 0, 0]
  Q_e := by rw [coe_QV]; decide
  Q_f := by rw [coe_QV]; decide
  polar_ef := by rw [polar_QV]; decide

theorem hp1_orth_hp2 : hp1.Orth hp2 where
  ee := by rw [polar_QV]; decide
  ef := by rw [polar_QV]; decide
  fe := by rw [polar_QV]; decide
  ff := by rw [polar_QV]; decide

theorem hp1_orth_hp3 : hp1.Orth hp3 where
  ee := by rw [polar_QV]; decide
  ef := by rw [polar_QV]; decide
  fe := by rw [polar_QV]; decide
  ff := by rw [polar_QV]; decide

theorem hp2_orth_hp3 : hp2.Orth hp3 where
  ee := by rw [polar_QV]; decide
  ef := by rw [polar_QV]; decide
  fe := by rw [polar_QV]; decide
  ff := by rw [polar_QV]; decide

theorem commutator_QV :
    ⁅TauCeti.QuadraticMap.orthogonalGroup QV, TauCeti.QuadraticMap.orthogonalGroup QV⁆ =
      elementaryGroup QV :=
  commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero (by decide) QV_nondeg
    hp1_orth_hp2 hp1_orth_hp3 hp2_orth_hp3


theorem OVq_eq_comap :
    OVq = (TauCeti.QuadraticMap.orthogonalGroup QV).comap
      (toLinEquiv (Fin 6) (ZMod 3)).toMonoidHom :=
  closure_isometries_eq_comap coe_QV

theorem mem_OVq_iff (g : GL6) :
    g ∈ OVq ↔ toLinEquiv (Fin 6) (ZMod 3) g ∈ TauCeti.QuadraticMap.orthogonalGroup QV := by
  rw [OVq_eq_comap]
  rfl

theorem mem_MDot_iff (g : GL6) :
    g ∈ MDot ↔ toLinEquiv (Fin 6) (ZMod 3) g ∈ elementaryGroup QV := by
  have : MDot = (elementaryGroup QV).comap (toLinEquiv (Fin 6) (ZMod 3)).toMonoidHom := by
    rw [← commutator_QV]
    exact statedOmega_eq_comap coe_QV
  rw [this]
  rfl


theorem bil_coord (u v : V6) : bil u v =
    2 * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4) - 2 * (u 5 * v 5) := by
  simp only [bil, qV, Pi.add_apply]
  ring

theorem bil_comm (u v : V6) : bil u v = bil v u := by
  rw [bil_coord, bil_coord]; ring

theorem bil_self (a : V6) : bil a a = 2 * qV a := by
  rw [bil_coord]; simp only [qV]; ring


theorem qV_sub_smul (x z : V6) (c : ZMod 3) :
    qV (x - c • z) = qV x - c * bil x z + c ^ 2 * qV z := by
  rw [bil_coord]
  simp only [qV, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem qV_mulVec_of_mem_OVq {g : GL6} (hg : g ∈ OVq) (v : V6) :
    qV ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = qV v :=
  qV_smul_of_mem_isometryCore hg v


@[expose] def wv (z : V6) : V6 := ![2 * z 0, 2 * z 1, 2 * z 2, 2 * z 3, 2 * z 4, 0 - 2 * z 5]

theorem dot_wv (z x : V6) : wv z ⬝ᵥ x = bil x z := by
  rw [bil_coord]; simp [dotProduct, Fin.sum_univ_six, wv]; ring

theorem dot_wv_self (z : V6) : wv z ⬝ᵥ z = 2 * qV z := by
  rw [dot_wv, bil_self]

@[expose] def reflM (z : V6) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  1 - (qV z)⁻¹ • Matrix.vecMulVec z (wv z)

theorem reflM_mulVec (z x : V6) : reflM z *ᵥ x = x - ((qV z)⁻¹ * bil x z) • z := by
  unfold reflM
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, dot_wv]
  simp [op_smul_eq_smul, smul_smul]

theorem reflM_mul_self (z : V6) (hz : qV z ≠ 0) : reflM z * reflM z = 1 := by
  have hμ : (qV z)⁻¹ * qV z = 1 := inv_mul_cancel₀ hz
  have hAA : Matrix.vecMulVec z (wv z) * Matrix.vecMulVec z (wv z) =
      (2 * qV z) • Matrix.vecMulVec z (wv z) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, dot_wv_self, Matrix.vecMulVec_smul]
  have hc : (qV z)⁻¹ * (qV z)⁻¹ * (2 * qV z) - (qV z)⁻¹ - (qV z)⁻¹ = 0 := by
    linear_combination (2 * (qV z)⁻¹) * hμ
  unfold reflM
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hAA, smul_smul]
  linear_combination (norm := module) hc • Matrix.vecMulVec z (wv z)

theorem qV_reflM (z x : V6) (hz : qV z ≠ 0) : qV (reflM z *ᵥ x) = qV x := by
  rw [reflM_mulVec, qV_sub_smul]
  have hμ : (qV z)⁻¹ * qV z = 1 := inv_mul_cancel₀ hz
  set b := bil x z
  linear_combination ((qV z)⁻¹ * b ^ 2) * hμ

@[expose] def refl6 (z : V6) (hz : qV z ≠ 0) : GL6 :=
  ⟨reflM z, reflM z, reflM_mul_self z hz, reflM_mul_self z hz⟩


theorem refl6_mulVec (z x : V6) (hz : qV z ≠ 0) :
    (refl6 z hz : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x = x - ((qV z)⁻¹ * bil x z) • z :=
  reflM_mulVec z x

theorem refl6_mem_OVq (z : V6) (hz : qV z ≠ 0) : refl6 z hz ∈ OVq :=
  Subgroup.subset_closure fun v => qV_reflM z v hz


theorem mat_eq_of_mulVec_eq {A B : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (h : ∀ x : V6, A *ᵥ x = B *ᵥ x) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun x => h x)


abbrev ReflVec : Type := {v : V6 // qV v ≠ 0}

@[expose] def reflOf (v : ReflVec) : GL6 := refl6 v.1 v.2

theorem QV_apply (v : V6) : QV v = qV v := congrFun coe_QV v

@[instance_reducible]
private noncomputable def invQV (v : ReflVec) : Invertible (QV v.1) :=
  invertibleOfNonzero (by rw [QV_apply]; exact v.2)

private theorem QV_nondeg' : QV.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp QV_nondeg

private noncomputable def toO : ↥OVq →* ↥(TauCeti.QuadraticMap.orthogonalGroup QV) :=
  MonoidHom.codRestrict ((toLinEquiv (Fin 6) (ZMod 3)).toMonoidHom.comp OVq.subtype)
    (TauCeti.QuadraticMap.orthogonalGroup QV) fun g => (mem_OVq_iff g).mp g.2

private noncomputable def Φ' : ↥OVq →*
    (ZMod 3)ˣ × Multiplicative (TauCeti.SquareClassGroup (ZMod 3)) :=
  (CFSG.ClassicalInvolution.detSpinorNorm QV_nondeg').comp toO

private theorem mem_MDot_iff_Φ' (x : ↥OVq) : (x : GL6) ∈ MDot ↔ Φ' x = 1 :=
  (mem_MDot_iff _).trans
    ((CFSG.ClassicalInvolution.orthogonalGroup_index_four QV_nondeg hp1_orth_hp2 hp1_orth_hp3
      hp2_orth_hp3).2 (toO x))

private def rOVq (v : ReflVec) : ↥OVq := ⟨reflOf v, refl6_mem_OVq v.1 v.2⟩

private def epsU (v : ReflVec) : (ZMod 3)ˣ := Units.mk0 (qV v.1) v.2

private theorem toO_rOVq (v : ReflVec) :
    toO (rOVq v) = @TauCeti.QuadraticMap.reflectionOrthogonal _ _ _ _ _ QV v.1 (invQV v) := by
  letI := invQV v
  apply Subtype.ext
  rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  change toLinEquiv (Fin 6) (ZMod 3) (reflOf v) = _
  ext x
  rw [toLinEquiv_apply, reflOf, refl6_mulVec, TauCeti.QuadraticMap.reflection_apply, invOf_eq_inv,
    QV_apply, polar_QV, bil_comm v.1 x]

private theorem unitOfInvertible_QV (v : ReflVec) :
    @unitOfInvertible _ _ (QV v.1) (invQV v) = epsU v := by
  apply Units.ext
  simp [epsU, QV_apply]

private theorem Φ'_rOVq (v : ReflVec) :
    Φ' (rOVq v) = (-1, TauCeti.squareClassHom (epsU v)) := by
  letI := invQV v
  rw [Φ', MonoidHom.comp_apply, toO_rOVq,
    CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal, unitOfInvertible_QV]

private theorem epsU_eq (v : ReflVec) : epsU v = if qV v.1 = -1 then -1 else 1 := by
  by_cases h : qV v.1 = -1
  · rw [if_pos h]
    apply Units.ext
    simp [epsU, h]
  · rw [if_neg h]
    apply Units.ext
    have h3 : ∀ a : ZMod 3, a ≠ 0 → a ≠ -1 → a = 1 := by decide
    have h1 : qV v.1 = 1 := h3 _ v.2 h
    simp [epsU, h1]

private theorem epsU_prod (l : List ReflVec) :
    (l.map epsU).prod = (-1 : (ZMod 3)ˣ) ^ (l.countP fun v => qV v.1 = -1) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.countP_cons, epsU_eq]
    by_cases h : qV v.1 = -1 <;> simp [h, pow_succ, mul_comm]

private theorem Φ'_prod (l : List ReflVec) :
    Φ' ((l.map rOVq).prod) = ((-1 : (ZMod 3)ˣ) ^ l.length,
      TauCeti.squareClassHom ((l.map epsU).prod)) := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, map_one, List.length_nil, pow_zero, List.map_nil,
      List.prod_nil, map_one]
    rfl
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Φ'_rOVq, ih, List.length_cons, List.map_cons,
      List.prod_cons, map_mul, pow_succ', Prod.mk_mul_mk]

private theorem squareClassHom_neg_one_pow (k : ℕ) :
    TauCeti.squareClassHom ((-1 : (ZMod 3)ˣ) ^ k) = 1 ↔ Even k := by
  rw [TauCeti.squareClassHom_apply, ofAdd_eq_one, TauCeti.squareClass_eq_zero_iff]
  constructor
  · intro h
    by_contra hk
    rw [Nat.not_even_iff_odd] at hk
    rw [hk.neg_one_pow] at h
    exact (by decide : ¬ IsSquare (-1 : (ZMod 3)ˣ)) h
  · intro hk
    rw [hk.neg_one_pow]
    exact ⟨1, by simp⟩

theorem prod_refl_mem_MDot_iff (l : List ReflVec) :
    (l.map reflOf).prod ∈ MDot ↔ Even l.length ∧ Even (l.countP fun v => qV v.1 = -1) := by
  have hprod : ((l.map rOVq).prod : GL6) = (l.map reflOf).prod := by
    rw [SubmonoidClass.coe_list_prod, List.map_map]
    rfl
  rw [← hprod, mem_MDot_iff_Φ', Φ'_prod, Prod.mk_eq_one, epsU_prod,
    neg_one_pow_eq_one_iff_even (by decide), squareClassHom_neg_one_pow]


theorem qV_xvec_ne_zero (i : Fin 6) : qV (xvec i) ≠ 0 := by
  fin_cases i <;> decide

theorem refl6_xvec_mulVec (i : Fin 6) (x : V6) :
    (refl6 (xvec i) (qV_xvec_ne_zero i) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x =
      Function.update x i (-x i) := by
  rw [refl6_mulVec]
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [xvec, qV, bil_coord, Function.update_apply, Pi.single_apply] <;> ring


end

end CFSG.Quasithin.SimsF5
