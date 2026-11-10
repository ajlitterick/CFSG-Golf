module

public meta import CFSG.Monster.B.Classical.UnitarySixForm
public meta import CFSG.Monster.B.Classical.UnitarySixBeta
public meta import CFSG.Monster.B.TwoA.Unitary.Form
public import Certificates.Certificate3141
import all CFSG.Fischer.F4

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
open CFSG.Monster.B.Classical.UnitarySix

theorem outA_det : outA.det = 1 :=
  Certificates.certificate3141.1

theorem outA_iso :
    (outA.map bar)ᵀ * antidiag 6 * outA = antidiag 6 :=
  Certificates.certificate3141.2.1

theorem outN_det : outN.det = 1 :=
  Certificates.certificate3141.2.2.1

theorem outN_iso :
    (outN.map bar)ᵀ * antidiag 6 * outN = antidiag 6 :=
  Certificates.certificate3141.2.2.2.1

theorem outA_beta : outA * betaM outA = 1 :=
  Certificates.certificate3141.2.2.2.2.1

theorem outN_A : outN * outA * betaM outN = outA :=
  Certificates.certificate3141.2.2.2.2.2.1

theorem outNPow_zero : outN * outN = outNPow 0 :=
  Certificates.certificate3141.2.2.2.2.2.2.1

theorem outNPow_one : outNPow 0 * outNPow 0 = outNPow 1 :=
  Certificates.certificate3141.2.2.2.2.2.2.2.1

theorem outNPow_two : outNPow 1 * outNPow 1 = outNPow 2 :=
  Certificates.certificate3141.2.2.2.2.2.2.2.2.1

theorem outNPow_eleven : outNPow 2 * outNPow 0 * outN = 1 :=
  Certificates.certificate3141.2.2.2.2.2.2.2.2.2

theorem outN_pow : outN ^ 11 = 1 := by
  have h2 : outN ^ 2 = outNPow 0 := by rw [sq, outNPow_zero]
  have h4 : outN ^ 4 = outNPow 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, h2, sq, outNPow_one]
  have h8 : outN ^ 8 = outNPow 2 := by
    rw [show 8 = 4 * 2 from rfl, pow_mul, h4, sq, outNPow_two]
  rw [show 11 = 8 + 2 + 1 from rfl, pow_add, pow_add, pow_one, h8, h2, outNPow_eleven]

theorem outN_ne : outN 0 3 ≠ 0 := by decide

@[expose] noncomputable def outASU : SU frobeniusF4 6 :=
  mkSU outA outA_det ((isIsometry_iff_map_bar _).2 outA_iso)

@[expose] noncomputable def outNSU : SU frobeniusF4 6 :=
  mkSU outN outN_det ((isIsometry_iff_map_bar _).2 outN_iso)

@[expose] noncomputable def phiL : LBeta :=
    ⟨(outASU : ProjSU), Multiplicative.ofAdd 1⟩

@[expose] noncomputable def nuL : LBeta := SemidirectProduct.inl
    (outNSU : ProjSU)

theorem betaHom_ofAdd_one : betaHom (Multiplicative.ofAdd 1) = betaL := by
  change betaPow 1 = betaL
  rw [betaPow, ite_eq_right (by decide)]

theorem phiL_mul_self : phiL * phiL = 1 := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [SemidirectProduct.mul_left, phiL, betaHom_ofAdd_one, betaL_mk, ← QuotientGroup.mk_mul,
      SemidirectProduct.one_left, ← QuotientGroup.mk_one]
    congr 1
    refine SU_ext ?_
    rw [coe_SU_mul, coe_betaSU, outASU, coe_mkSU, outA_beta, coe_SU_one]
  · rw [SemidirectProduct.mul_right, phiL, SemidirectProduct.one_right]
    show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1
    decide

theorem outNSU_pow : outNSU ^ 11 = 1 := by
  refine SU_ext ?_
  rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, outNSU, coe_mkSU, outN_pow, coe_SU_one]

theorem nuL_pow : nuL ^ 11 = 1 := by
  rw [nuL, ← map_pow, ← QuotientGroup.mk_pow, outNSU_pow, QuotientGroup.mk_one, map_one]

theorem nuL_ne_one : nuL ≠ 1 := by
  intro h
  have h1 : (outNSU : ProjSU) = 1 := SemidirectProduct.inl_injective (h.trans (map_one _).symm)
  rw [QuotientGroup.eq_one_iff, mem_scalars] at h1
  obtain ⟨a, ha⟩ := h1
  have h2 := congrFun (congrFun ha 0) 3
  rw [outNSU, coe_mkSU, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)] at h2
  exact outN_ne h2

theorem nuL_phiL_nuL : nuL * phiL * nuL = phiL := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right]
    simp only [nuL, phiL, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one,
      MulAut.one_apply, one_mul]
    rw [betaHom_ofAdd_one, betaL_mk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    refine SU_ext ?_
    rw [coe_SU_mul, coe_SU_mul, coe_betaSU, outNSU, outASU, coe_mkSU, coe_mkSU, outN_A]
  · simp [nuL, phiL]

theorem phiL_conj_nuL : phiL * nuL * phiL⁻¹ = nuL⁻¹ := by
  have h1 : phiL⁻¹ = phiL := inv_eq_of_mul_eq_one_right phiL_mul_self
  rw [h1]
  calc phiL * nuL * phiL = nuL⁻¹ * (nuL * phiL * nuL) * phiL := by group
    _ = nuL⁻¹ := by rw [nuL_phiL_nuL, mul_assoc, phiL_mul_self, mul_one]

open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std.FieldExtension
  CFSG.LieType.Chevalley.C2E6Std CFSG.Blueprint.Chevalley

noncomputable abbrev leviEmb :
    LBeta →* GStar :=
  leviStar.subtype.comp leviStarEquiv.symm.toMonoidHom

theorem leviEmb_injective :
    Function.Injective leviEmb :=
  Subtype.val_injective.comp leviStarEquiv.symm.injective

theorem leviEmb_mem_centralizer
    (x : LBeta) : leviEmb x ∈
    centralizer {rootStar} := by
  rw [centralizer_rootStar, mem_parStar]
  exact stdLevi_le_nativeParabolic two_mem_firstJ (mem_leviStar.1 (leviStarEquiv.symm x).2)

theorem leviEmb_right_ne_one
    {x : LBeta} (hx : x.right ≠ 1) :
    (leviEmb x).right ≠ 1 := by
  intro h
  have h1 : (leviStarEquiv (leviStarEquiv.symm x)).right =
      betaIdx ((leviStarEquiv.symm x : leviStar) : GStar).right := leviStarHom_right _
  rw [MulEquiv.apply_symm_apply] at h1
  have h2 : ((leviStarEquiv.symm x : leviStar) : GStar).right = 1 := h
  rw [h2, map_one] at h1
  exact hx h1

theorem conj_commute {M : Type*} [Group M] {a b : M} (h : Commute a b) (g : M) :
    Commute (g * a * g⁻¹) (g * b * g⁻¹) := by
  change g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [h.eq]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem exists_outer_inverting_star
    {t' : stdGroup}
    (ht' : t' ∈ CFSG.Monster.B.E6.StdF4.rootClass) :
    ∃ φ ν : GStar, φ * φ = 1 ∧ φ.right ≠ 1 ∧ Commute φ (SemidirectProduct.inl t') ∧
      ν ^ 11 = 1 ∧ ν ≠ 1 ∧ Commute ν (SemidirectProduct.inl t') ∧ φ * ν * φ⁻¹ = ν⁻¹ := by
  obtain ⟨h, hh⟩ := isConj_iff.1 ht'
  have ht : (SemidirectProduct.inl t' : GStar) =
      SemidirectProduct.inl h * rootStar * (SemidirectProduct.inl h)⁻¹ := by
    rw [← hh, rootStar, map_mul, map_mul, map_inv]
  set g : GStar := SemidirectProduct.inl h
  have hc : ∀ x : LBeta, Commute (leviEmb x) rootStar := fun x =>
    (mem_centralizer_singleton_iff.1 (leviEmb_mem_centralizer x))
  refine ⟨g * leviEmb phiL * g⁻¹, g * leviEmb nuL * g⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc g * leviEmb phiL * g⁻¹ * (g * leviEmb phiL * g⁻¹) = g * (leviEmb (phiL * phiL)) * g⁻¹ := by
          rw [map_mul]; group
      _ = 1 := by rw [phiL_mul_self, map_one]; group
  · have e : (g * leviEmb phiL * g⁻¹).right = (leviEmb phiL).right := by
      simp only [g, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
        SemidirectProduct.right_inl, inv_one, one_mul, mul_one]
    rw [e]
    exact leviEmb_right_ne_one (by rw [phiL]; exact ofAdd_one_ne_one)
  · rw [ht]
    exact conj_commute (hc phiL) g
  · rw [conj_pow, ← map_pow, nuL_pow, map_one, mul_one, mul_inv_cancel]
  · intro h1
    apply nuL_ne_one
    apply leviEmb_injective
    rw [map_one]
    calc leviEmb nuL = g⁻¹ * (g * leviEmb nuL * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · rw [ht]
    exact conj_commute (hc nuL) g
  · calc g * leviEmb phiL * g⁻¹ * (g * leviEmb nuL * g⁻¹) * (g * leviEmb phiL * g⁻¹)⁻¹ =
        g * (leviEmb (phiL * nuL * phiL⁻¹)) * g⁻¹ := by rw [map_mul, map_mul, map_inv]; group
      _ = (g * leviEmb nuL * g⁻¹)⁻¹ := by rw [phiL_conj_nuL, map_inv]; group

open CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.GSide

theorem map_xhatEam
    {ρ : vStab cv0 →* GStar}
    {iv : cgraph.neighborSet cv0 ≃ CFSG.Monster.B.E6.StdF4.rootClass}
    (hρ : IsCompatLocal cv0 ρ iv) :
    ρ (vStabEam.symm xhatEam) =
      SemidirectProduct.inl (iv ⟨cw0, cgraph_adj_cv0_cw0⟩ : stdGroup) := by
  rw [← vStabEam_cV0_mul_lamW0H, MulEquiv.symm_apply_apply, map_mul]
  have h1 : ρ cV0 = 1 := (hρ.2.1 cV0).2 (by rw [coe_cV0, coe_clabelS]; exact mem_zpowers _)
  rw [h1, one_mul]
  exact hρ.2.2.2.2 ⟨cw0, cgraph_adj_cv0_cw0⟩ lamW0H rfl

theorem cE'_mul_self :
    cE' * cE' = 1 := by
  rw [← sq, ← orderOf_cE', pow_orderOf_eq_one]

theorem exists_outer_involution_inverting :
    ∃ e ν : Eam, e ∈ centralizer ({xhatEam} : Set Eam) ∧ ν ∈ centralizer ({xhatEam} : Set Eam) ∧
      e ∉ commutator Eam ∧ e * e = 1 ∧ orderOf ν = 11 ∧ e * ν * e⁻¹ = ν⁻¹ := by
  obtain ⟨ρ, iv, hρ⟩ := exists_isCompatLocal cv0
  obtain ⟨φ, ν, hφ2, hφr, hφt, hν11, hν1, hνt, hφν⟩ :=
    exists_outer_inverting_star (iv ⟨cw0, cgraph_adj_cv0_cw0⟩).2
  rw [← map_xhatEam hρ] at hφt hνt
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : Eam →* GStar, ρ' = ρ.comp vStabEam.symm.toMonoidHom := ⟨_, rfl⟩
  have hρy : ∀ y, ρ' y = ρ (vStabEam.symm y) := fun y => by rw [hρ']; rfl
  rw [← hρy] at hφt hνt
  have hsurj : Function.Surjective ρ' := by
    rw [hρ']
    exact hρ.1.comp vStabEam.symm.surjective
  have hker : ∀ w : Eam, ρ' w = 1 → w = 1 ∨ w = cE' := fun w hw =>
    eq_one_or_eq_cE'_of_map_eq_one hρ ((hρy w).symm.trans hw)
  have hc : ∀ y : Eam, y * cE' = cE' * y := fun y =>
    Subgroup.mem_center_iff.1 cE'_mem_center y
  have hcomm : ∀ y : Eam, Commute (ρ' y) (ρ' xhatEam) →
      y ∈ centralizer ({xhatEam} : Set Eam) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    have h1 : ρ' (y * xhatEam * y⁻¹ * xhatEam⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy.eq]
      group
    rcases hker _ h1 with h | h
    · have e : y * xhatEam * y⁻¹ = xhatEam := mul_inv_eq_one.1 h
      calc y * xhatEam = y * xhatEam * y⁻¹ * y := by group
        _ = xhatEam * y := by rw [e]
    · exact absurd (isConj_iff.2 ⟨y, mul_inv_eq_iff_eq_mul.1 h⟩) not_isConj_xhatEam
  obtain ⟨e, he⟩ := hsurj φ
  obtain ⟨ν₀, hν₀⟩ := hsurj ν
  have hν2 : ρ' (ν₀ * ν₀) = ν * ν := by rw [map_mul, hν₀]
  have hνν : ν * ν ≠ 1 := by
    intro h
    apply hν1
    calc ν = ν * (ν * ν) ^ 5 := by rw [h, one_pow, mul_one]
      _ = ν ^ 11 := by rw [← sq, ← pow_mul, ← pow_succ']
      _ = 1 := hν11
  have h11 : (ν₀ * ν₀) ^ 11 = 1 := by
    have e1 : (ν₀ * ν₀) ^ 11 = ν₀ ^ 11 * ν₀ ^ 11 := by rw [← sq, ← pow_mul, ← pow_add]
    rcases hker (ν₀ ^ 11) (by rw [map_pow, hν₀, hν11]) with h | h
    · rw [e1, h, mul_one]
    · rw [e1, h, cE'_mul_self]
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine ⟨e, ν₀ * ν₀, hcomm e (by rw [he]; exact hφt),
    hcomm _ (by rw [hν2]; exact hνt.mul_left hνt), ?_, ?_,
    orderOf_eq_prime h11 (fun h => hνν (by rw [← hν2, h, map_one])), ?_⟩
  · intro heE
    apply hφr
    have hmap : (commutator Eam).map ρ' = CFSG.Monster.B.E6.Ginl := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.2 hsurj, ← _root_.commutator_def,
        CFSG.Monster.B.E6.commutator_GStar]
    have hmem : ρ' e ∈ (commutator Eam).map ρ' := mem_map_of_mem _ heE
    rw [hmap] at hmem
    obtain ⟨x, hx⟩ := hmem
    rw [← he, ← hx, SemidirectProduct.right_inl]
  · rcases hker (e * e) (by rw [map_mul, he, hφ2]) with h | h
    · exact h
    · exact absurd h (mul_self_ne_cE' e)
  · have h1 : ρ' (e * (ν₀ * ν₀) * e⁻¹ * (ν₀ * ν₀)) = 1 := by
      simp only [map_mul, map_inv, he, hν₀]
      calc φ * (ν * ν) * φ⁻¹ * (ν * ν) = (φ * ν * φ⁻¹) * (φ * ν * φ⁻¹) * (ν * ν) := by group
        _ = 1 := by rw [hφν]; group
    rcases hker _ h1 with h | h
    · exact mul_eq_one_iff_eq_inv.1 h
    · exfalso
      have e1 : e * (ν₀ * ν₀) * e⁻¹ = cE' * (ν₀ * ν₀)⁻¹ := eq_mul_inv_iff_mul_eq.2 h
      have e2 : (e * (ν₀ * ν₀) * e⁻¹) ^ 11 = 1 := by rw [conj_pow, h11, mul_one, mul_inv_cancel]
      rw [e1, (Commute.mul_pow (hc _).symm 11), inv_pow, h11, inv_one, mul_one] at e2
      apply cE'_ne_one
      calc cE' = cE' * (cE' * cE') ^ 5 := by rw [cE'_mul_self, one_pow, mul_one]
        _ = cE' ^ 11 := by rw [← sq, ← pow_mul, ← pow_succ']
        _ = 1 := e2

end CFSG.EvenSmallLie.TwoE6
