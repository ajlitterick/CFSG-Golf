
module

public import CFSG.Monster.B.TwoA.Co2Inv.KernelBase

public import CFSG.Monster.B.TwoA.Co2Inv.KerFix

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts

theorem qElt_comm_iff
    {e l t e' l' t' : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16)
    (he' : e' < 2) (hl' : l' < 16) (ht' : t' < 16) :
    qElt e l t * qElt e' l' t' = qElt e' l' t' * qElt e l t ↔
      par4 (l' &&& t) = par4 (l &&& t') := by
  rw [qElt_mul he hl ht he' hl' ht', qElt_mul he' hl' ht' he hl ht]
  constructor
  · intro h
    obtain ⟨h1, -, -⟩ := qElt_inj (xor_lt_two (xor_lt_two he he') (par4_lt _))
      (xor_lt_sixteen hl hl') (xor_lt_sixteen ht ht') (xor_lt_two (xor_lt_two he' he) (par4_lt _))
      (xor_lt_sixteen hl' hl) (xor_lt_sixteen ht' ht) h
    rw [Nat.xor_comm e' e] at h1
    exact xor_left_cancel' h1
  · intro h
    rw [h, Nat.xor_comm e e', Nat.xor_comm l l', Nat.xor_comm t t']

theorem qElt_inv_mul_same
    {a b L T : ℕ} (ha : a < 2) (hb : b < 2) (hL : L < 16) (hT : T < 16) :
    (qElt a L T)⁻¹ * qElt b L T = qElt (a ^^^ b) 0 0 := by
  rw [qElt_inv ha hL hT, qElt_mul (xor_lt_two ha (par4_lt _)) hL hT hb hL hT, xor_four,
    Nat.xor_self, Nat.xor_self]

@[expose] def qQ
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) : Qgrp :=
  ⟨qElt e l t, mem_Qgrp_iff.2 ⟨e, he, l, hl, t, ht, rfl⟩⟩

theorem exists_qQ
    (x : Qgrp) : ∃ e, ∃ he : e < 2, ∃ l, ∃ hl : l < 16, ∃ t, ∃ ht : t < 16,
    x = qQ he hl ht := by
  obtain ⟨e, he, l, hl, t, ht, h⟩ := mem_Qgrp_iff.1 x.2
  exact ⟨e, he, l, hl, t, ht, Subtype.ext h⟩

theorem qQ_mul
    {e l t e' l' t' : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) (he' : e' < 2)
    (hl' : l' < 16) (ht' : t' < 16) :
    qQ he hl ht * qQ he' hl' ht' = qQ (xor_lt_two (xor_lt_two he he') (par4_lt (l' &&& t)))
      (xor_lt_sixteen hl hl') (xor_lt_sixteen ht ht') :=
  Subtype.ext (qElt_mul he hl ht he' hl' ht')

theorem qQ_inj
    {e l t e' l' t' : ℕ} {he : e < 2} {hl : l < 16} {ht : t < 16} {he' : e' < 2}
    {hl' : l' < 16} {ht' : t' < 16} (h : qQ he hl ht = qQ he' hl' ht') :
    e = e' ∧ l = l' ∧ t = t' :=
  qElt_inj he hl ht he' hl' ht' (congrArg Subtype.val h)

theorem qQ_zero
    {he : 0 < 2} {hl : 0 < 16} {ht : 0 < 16} : qQ he hl ht = 1 :=
  Subtype.ext qElt_zero

theorem qQ_comm_iff
    {e l t e' l' t' : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) (he' : e' < 2)
    (hl' : l' < 16) (ht' : t' < 16) :
    qQ he hl ht * qQ he' hl' ht' = qQ he' hl' ht' * qQ he hl ht ↔
      par4 (l' &&& t) = par4 (l &&& t') :=
  Subtype.ext_iff.trans (qElt_comm_iff he hl ht he' hl' ht')

@[expose] def rQ :
    Qgrp := qQ (e := 1) (l := 0) (t := 0) (by norm_num) (by norm_num) (by norm_num)

theorem coe_rQ :
    ((rQ : Qgrp) : OLq) = (rK : OLq) := qElt_one_zero_zero

theorem rQ_ne_one :
    rQ ≠ 1 := by
  intro h
  rw [← qQ_zero (he := by norm_num) (hl := by norm_num) (ht := by norm_num)] at h
  exact absurd (qQ_inj h).1 (by norm_num)

theorem rQ_mem_center :
    rQ ∈ Subgroup.center Qgrp := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨e, he, l, hl, t, ht, rfl⟩ := exists_qQ g
  refine (qQ_comm_iff he hl ht (by norm_num) (by norm_num) (by norm_num)).2 ?_
  rw [par4_zero_left t ht, par4_zero_right l hl]

theorem qQ_mem_center
    {e : ℕ} (he : e < 2) {hl : 0 < 16} {ht : 0 < 16} :
    qQ he hl ht ∈ Subgroup.center Qgrp := by
  rcases eq_zero_or_one he with rfl | rfl
  · rw [qQ_zero]
    exact Subgroup.one_mem _
  · exact rQ_mem_center

theorem mem_center_Qgrp_iff
    (x : Qgrp) : x ∈ Subgroup.center Qgrp ↔ x = 1 ∨ x = rQ := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff] at h
    obtain ⟨e, he, l, hl, t, ht, rfl⟩ := exists_qQ x
    have ht0 : t = 0 := par4_sep_right t ht fun l' hl' => by
      have := (qQ_comm_iff (by norm_num : 0 < 2) hl' (by norm_num : 0 < 16) he hl ht).1 (h _)
      rw [par4_zero_right l hl] at this
      exact this.symm
    have hl0 : l = 0 := par4_sep_left l hl fun t' ht' => by
      have := (qQ_comm_iff (by norm_num : 0 < 2) (by norm_num : 0 < 16) ht' he hl ht).1 (h _)
      rw [par4_zero_left t ht] at this
      exact this
    subst ht0
    subst hl0
    rcases eq_zero_or_one he with rfl | rfl
    · exact Or.inl qQ_zero
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact rQ_mem_center

theorem center_Qgrp_eq_zpowers :
    Subgroup.center Qgrp = Subgroup.zpowers rQ := by
  refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.2 rQ_mem_center)
  rcases (mem_center_Qgrp_iff x).1 hx with rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers _

theorem natCard_center_Qgrp :
    Nat.card (Subgroup.center Qgrp) = 2 := by
  have h : ((Subgroup.center Qgrp : Subgroup Qgrp) : Set Qgrp) = {1, rQ} := by
    ext x
    rw [SetLike.mem_coe, mem_center_Qgrp_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_pair rQ_ne_one.symm]

theorem comm_mem_center
    (x y : Qgrp) : (x * y)⁻¹ * (y * x) ∈ Subgroup.center Qgrp := by
  obtain ⟨e, he, l, hl, t, ht, rfl⟩ := exists_qQ x
  obtain ⟨e', he', l', hl', t', ht', rfl⟩ := exists_qQ y
  rw [qQ_mul, qQ_mul]
  have h : (qQ (xor_lt_two (xor_lt_two he he') (par4_lt (l' &&& t))) (xor_lt_sixteen hl hl')
      (xor_lt_sixteen ht ht'))⁻¹ * qQ (xor_lt_two (xor_lt_two he' he) (par4_lt (l &&& t')))
      (xor_lt_sixteen hl' hl) (xor_lt_sixteen ht' ht) =
      qQ (xor_lt_two (xor_lt_two (xor_lt_two he he') (par4_lt (l' &&& t)))
        (xor_lt_two (xor_lt_two he' he) (par4_lt (l &&& t')))) (by norm_num : 0 < 16)
        (by norm_num : 0 < 16) := by
    apply Subtype.ext
    change (qElt _ _ _)⁻¹ * qElt _ _ _ = qElt _ _ _
    rw [Nat.xor_comm l' l, Nat.xor_comm t' t]
    exact qElt_inv_mul_same (xor_lt_two (xor_lt_two he he') (par4_lt _))
      (xor_lt_two (xor_lt_two he' he) (par4_lt _)) (xor_lt_sixteen hl hl')
      (xor_lt_sixteen ht ht')
  rw [h]
  exact qQ_mem_center _

theorem sq_mem_center
    (x : Qgrp) : x ^ 2 ∈ Subgroup.center Qgrp := by
  obtain ⟨e, he, l, hl, t, ht, rfl⟩ := exists_qQ x
  have h : qQ he hl ht ^ 2 = qQ (par4_lt (l &&& t)) (by norm_num : 0 < 16)
      (by norm_num : 0 < 16) :=
    Subtype.ext ((pow_two _).trans (qElt_sq he hl ht))
  rw [h]
  exact qQ_mem_center _

theorem isElementaryAbelian_quotient_center :
    IsElementaryAbelian 2 (Qgrp ⧸ Subgroup.center Qgrp) := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        exact comm_mem_center x y
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact sq_mem_center x

theorem qQ_one_not_mem_center :
    qQ (e := 0) (l := 1) (t := 0) (by norm_num) (by norm_num) (by norm_num) ∉
      Subgroup.center Qgrp := by
  rw [mem_center_Qgrp_iff]
  rintro (h | h)
  · rw [← qQ_zero (he := by norm_num) (hl := by norm_num) (ht := by norm_num)] at h
    exact absurd (qQ_inj h).2.1 (by norm_num)
  · exact absurd (qQ_inj h).2.1 (by norm_num)

theorem isExtraspecial_Qgrp :
    CFSG.IsExtraspecial 2 Qgrp :=
  ⟨natCard_center_Qgrp, isElementaryAbelian_quotient_center,
    ⟨⟨QuotientGroup.mk (qQ (e := 0) (l := 1) (t := 0) (by norm_num) (by norm_num)
      (by norm_num)), 1, fun h => qQ_one_not_mem_center ((QuotientGroup.eq_one_iff _).1 h)⟩⟩⟩

theorem isExtraspecialPGroup_Qgrp :
    IsExtraspecialPGroup 2 Qgrp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Qgrp := Nat.finite_of_card_ne_zero (by rw [natCard_Qgrp]; norm_num)
  exact isExtraspecialPGroup_iff_isExtraspecial.2 isExtraspecial_Qgrp

theorem exists_params
    (x : Qgrp) : ∃ p : ℕ × ℕ × ℕ, p.1 < 2 ∧ p.2.1 < 16 ∧ p.2.2 < 16 ∧
    (x : OLq) = qElt p.1 p.2.1 p.2.2 := by
  obtain ⟨e, he, l, hl, t, ht, h⟩ := mem_Qgrp_iff.1 x.2
  exact ⟨(e, l, t), he, hl, ht, h⟩

@[expose] def qPar
    (x : Qgrp) : ℕ × ℕ × ℕ := (exists_params x).choose

theorem qPar_qQ
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) :
    qPar (qQ he hl ht) = (e, l, t) := by
  obtain ⟨h1, h2, h3, h4⟩ := (exists_params (qQ he hl ht)).choose_spec
  obtain ⟨a, b, c⟩ := qElt_inj h1 h2 h3 he hl ht h4.symm
  exact Prod.ext a (Prod.ext b c)

@[expose] def phiFun
    (x : Qgrp) : Multiplicative ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :=
  Multiplicative.ofAdd (bvec 4 (qPar x).2.1, bvec 4 (qPar x).2.2)

theorem phiFun_qQ
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) :
    phiFun (qQ he hl ht) = Multiplicative.ofAdd (bvec 4 l, bvec 4 t) := by
  rw [phiFun, qPar_qQ]

theorem phiFun_mul
    (x y : Qgrp) : phiFun (x * y) = phiFun x * phiFun y := by
  obtain ⟨e, he, l, hl, t, ht, rfl⟩ := exists_qQ x
  obtain ⟨e', he', l', hl', t', ht', rfl⟩ := exists_qQ y
  rw [qQ_mul, phiFun_qQ, phiFun_qQ, phiFun_qQ, bvec_xor, bvec_xor, ← ofAdd_add, Prod.mk_add_mk]

@[expose] def phiQ :
    Qgrp →* Multiplicative ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :=
  MonoidHom.mk' phiFun phiFun_mul


end CFSG.Monster.B.TwoA.Co2Inv
