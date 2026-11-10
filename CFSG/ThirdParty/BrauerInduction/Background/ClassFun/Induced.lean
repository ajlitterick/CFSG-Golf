module

public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Maps
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Coset

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Induction of class functions

This file defines induction of class functions from a subgroup `H ≤ G` to `G`.

The definition is given by summing the usual conjugation summand over coset
representatives. The file proves the basic algebraic properties of induction:
additivity, compatibility with scalar multiplication, transitivity, the
projection formula, compatibility with coefficient maps, and the standard
averaging formula over the whole group.
-/

namespace CFSG.ClassFun

section Summand

variable {k : Type u} [Zero k]
variable {G : Type v} [Group G]

open Classical in
/--
The summand appearing in the induced class function.
-/
@[expose] noncomputable def indSummand
    (H : Subgroup G) (φ : ClassFun k H) (g x : G) : k :=
  if hx : x⁻¹ * g * x ∈ H then
    φ ⟨x⁻¹ * g * x, hx⟩
  else
    0

private lemma indSummand_mul_right
    (H : Subgroup G) (φ : ClassFun k H)
    (g x : G) (h : H) :
    indSummand H φ g (x * (h : G)) =
      indSummand H φ g x := by
  unfold indSummand
  have halg :
      (x * (h : G))⁻¹ * g * (x * (h : G)) =
        (h⁻¹ : H).val * (x⁻¹ * g * x) * (h : H).val := by
    simp only [mul_inv_rev, InvMemClass.coe_inv]
    group
  by_cases hx : x⁻¹ * g * x ∈ H
  · have hxh :
        (x * (h : G))⁻¹ * g * (x * (h : G)) ∈ H :=
      halg.symm ▸
        H.mul_mem
          (H.mul_mem (H.inv_mem h.property) hx)
          h.property
    simp only [dif_pos hx, dif_pos hxh]
    have hconj :
        IsConj
          (⟨(x * (h : G))⁻¹ * g * (x * (h : G)), hxh⟩ : H)
          (⟨x⁻¹ * g * x, hx⟩ : H) := by
      rw [isConj_iff]
      use h
      ext
      push_cast
      rw [halg]
      simp only [InvMemClass.coe_inv]
      group
    exact φ.map_conj _ _ hconj
  · have hxh :
        (x * (h : G))⁻¹ * g * (x * (h : G)) ∉ H := by
      intro hmem
      apply hx
      have halg_inv :
          x⁻¹ * g * x =
            (h : H).val *
              ((x * (h : G))⁻¹ * g * (x * (h : G))) *
              (h⁻¹ : H).val := by
        simp only [mul_inv_rev, InvMemClass.coe_inv]
        group
      exact halg_inv.symm ▸
        H.mul_mem
          (H.mul_mem h.property hmem)
          (H.inv_mem h.property)
    simp only [dif_neg hx, dif_neg hxh]

open Classical in
private lemma indSummand_conj_mul_left
    (H : Subgroup G) (φ : ClassFun k H)
    {x y : G} (a z : G)
    (ha : a * x * a⁻¹ = y) :
    indSummand H φ y (a * z) =
      indSummand H φ x z := by
  unfold indSummand
  have harg :
      (a * z)⁻¹ * y * (a * z) =
        z⁻¹ * x * z := by
    rw [← ha]
    group
  rw [harg]

open Classical in
private lemma indSummand_smul_quotient
    (H : Subgroup G) (φ : ClassFun k H)
    {x y : G} (a : G)
    (ha : a * x * a⁻¹ = y)
    (q : G ⧸ H) :
    indSummand H φ y (a • q).out =
      indSummand H φ x q.out := by
  have hq :
      (a • q : G ⧸ H) =
        (↑(a * q.out) : G ⧸ H) := by
    rw [← QuotientGroup.out_eq' q]
    simpa using
      (MulAction.Quotient.smul_mk H a q.out)
  obtain ⟨h, hout⟩ :=
    QuotientGroup.mk_out_eq_mul H (a * q.out)
  have hout' :
      (a • q).out =
        a * q.out * (h : G) := by
    rw [hq]
    exact hout
  calc
    indSummand H φ y (a • q).out
        =
      indSummand H φ y
        ((a * q.out) * (h : G)) := by
          rw [hout']
    _ =
      indSummand H φ y (a * q.out) :=
        indSummand_mul_right H φ y (a * q.out) h
    _ =
      indSummand H φ x q.out :=
        indSummand_conj_mul_left H φ a q.out ha

end Summand

section Induction

variable {k : Type u} [AddCommMonoid k]
variable {G : Type v} [Group G] [Finite G]

noncomputable local instance instFintypeG : Fintype G :=
  Fintype.ofFinite G

open Classical in

/--
Induced class function, defined by summing the usual conjugation summand over
the quotient `G ⧸ H`.
-/
@[expose] noncomputable def ind
    (H : Subgroup G) (φ : ClassFun k H) :
    ClassFun k G where
  toFun g :=
    ∑ q : G ⧸ H, indSummand H φ g q.out
  map_conj := by
    intro x y hxy
    rw [isConj_iff] at hxy
    rcases hxy with ⟨a, ha⟩
    let e : G ⧸ H ≃ G ⧸ H := {
      toFun q := a • q
      invFun q := a⁻¹ • q
      left_inv q := by
        simp [smul_smul]
      right_inv q := by
        simp [smul_smul]
    }
    nth_rewrite 2 [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro q _
    dsimp [e]
    exact (indSummand_smul_quotient H φ a ha q).symm

open Classical in
/--
The defining formula for the induced class function.
-/
@[simp]
lemma ind_apply
    (H : Subgroup G) (φ : ClassFun k H) (g : G) :
    ind H φ g =
      ∑ q : G ⧸ H,
        if hx : q.out⁻¹ * g * q.out ∈ H then
          φ ⟨q.out⁻¹ * g * q.out, hx⟩
        else
          0 :=
  rfl

open Classical in

/--
Alternative formula for induction as a sum over the explicit right-coset
quotient.

The equivalence with the defining quotient is induced by inversion, so the
conjugate `x⁻¹ * g * x` becomes `x * g * x⁻¹`.
-/
lemma ind_apply_rightCosets
    (H : Subgroup G) (φ : ClassFun k H) (g : G) :
    ind H φ g =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        if hx : q.out * g * q.out⁻¹ ∈ H then
          φ ⟨q.out * g * q.out⁻¹, hx⟩
        else
          0 := by
  rw [ind_apply]
  let e :
      Quotient (QuotientGroup.rightRel H) ≃ G ⧸ H :=
    QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  change
    (∑ p : G ⧸ H, indSummand H φ g p.out) =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        if hx : q.out * g * q.out⁻¹ ∈ H then
          φ ⟨q.out * g * q.out⁻¹, hx⟩
        else
          0
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro q _
  have heq :
      e q = (↑(q.out⁻¹) : G ⧸ H) := by
    calc
      e q = e (Quotient.mk (QuotientGroup.rightRel H) q.out) := by
        exact congrArg e (Quotient.out_eq q).symm
      _ = (↑(q.out⁻¹) : G ⧸ H) := by
        rfl
  obtain ⟨h, hout⟩ := QuotientGroup.mk_out_eq_mul H q.out⁻¹
  have hout' : (e q).out = q.out⁻¹ * (h : G) := by
    rw [heq]
    exact hout
  calc
    indSummand H φ g (e q).out
        =
      indSummand H φ g (q.out⁻¹ * (h : G)) := by
        rw [hout']
    _ =
      indSummand H φ g q.out⁻¹ :=
        indSummand_mul_right H φ g q.out⁻¹ h
    _ =
      if hx : q.out * g * q.out⁻¹ ∈ H then
        φ ⟨q.out * g * q.out⁻¹, hx⟩
      else
        0 := by
      unfold indSummand
      simp only [inv_inv]

/--
Induction is additive.
-/
@[simp]
theorem ind_add {H : Subgroup G} (φ ψ : ClassFun k H) :
    ind H (φ + ψ) = ind H φ + ind H ψ := by
  ext g
  simp only [ind_apply, add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp


/--
Induction sends the zero class function to zero.
-/
@[simp]
theorem ind_zero {H : Subgroup G} :
    ind H (0 : ClassFun k H) = 0 := by
  ext g
  simp [ind_apply, zero_apply, Finset.sum_const_zero]

end Induction

section ScalarAction

variable {R : Type w} [Semiring R]
variable {k : Type u} [AddCommMonoid k] [Module R k]
variable {G : Type v} [Group G]


/--
Induction commutes with scalar multiplication.
-/
@[simp]
theorem ind_smul [Finite G]
    {H : Subgroup G} (r : R) (φ : ClassFun k H) :
    ind H (r • φ) = r • ind H φ := by
  ext g
  simp only [ind_apply, smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q.out⁻¹ * g * q.out ∈ H
  · simp only [hq, ↓reduceDIte]
  · simp only [hq, ↓reduceDIte, smul_zero]

/--
Induction of class functions from `H` to `G`, regarded as a linear map.
-/
@[expose] noncomputable def indLinearMap [Finite G]
    (H : Subgroup G) :
    ClassFun k H →ₗ[R] ClassFun k G where
  toFun := ind H
  map_add' φ ψ := by
    simp only [ind_add (H := H) φ ψ]
  map_smul' r φ := by
    simp only [ind_smul (R := R) (H := H) r φ, RingHom.id_apply]

/--
Evaluation of `indLinearMap`.
-/
@[simp]
lemma indLinearMap_apply [Finite G]
    (H : Subgroup G) (φ : ClassFun k H) :
    indLinearMap (R := R) H φ = ind H φ :=
  rfl

end ScalarAction

section AdditiveGroup

variable {k : Type u} [AddCommGroup k]
variable {G : Type v} [Group G] [Finite G]

/--
Induction commutes with integer scalar multiplication.
-/
@[simp]
theorem ind_zsmul
    {H : Subgroup G} (n : ℤ) (φ : ClassFun k H) :
    ind H (n • φ) = n • ind H φ := by
  letI: Fintype G := Fintype.ofFinite G
  exact ind_smul n φ

end AdditiveGroup

section AveragingFormula

variable {k : Type u} [Field k] [CharZero k]
variable {G : Type v} [Group G] [Fintype G]


end AveragingFormula

section Transitivity

variable {k : Type u} [AddCommMonoid k]
variable {G : Type v} [Group G]


end Transitivity

section ProjectionFormula

variable {k : Type u} [Semiring k]
variable {G : Type v} [Group G] [Finite G]

open Classical in

/--
The projection formula for class-function induction.

Multiplication by a class function on `G` commutes with induction after
restricting that class function to the subgroup.
-/
lemma projection_formula
    (H : Subgroup G)
    (ψ : ClassFun k G)
    (χ : ClassFun k H) :
    ψ * ind H χ = ind H (res H ψ * χ) := by
  ext g
  simp only [mul_apply, ind_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q.out⁻¹ * g * q.out ∈ H
  · simp only [dif_pos hq, res_apply]
    rw [map_conj_eq]
  · simp only [dif_neg hq, mul_zero]

end ProjectionFormula

section CoefficientMaps

variable {R : Type u} {S : Type w}
variable [AddCommMonoid R] [AddCommMonoid S]
variable {G : Type v} [Group G] [Finite G]

open Classical in
/--
Induction commutes with postcomposition by an additive homomorphism of
coefficient types.
-/
@[simp]
lemma ind_postcomp
    (F : R →+ S)
    (H : Subgroup G)
    (φ : ClassFun R H) :
    ind H (φ.postcomp F) =
      (ind H φ).postcomp F := by
  ext g
  simp only [ind_apply, postcomp_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q.out⁻¹ * g * q.out ∈ H
  · simp only [hq, ↓reduceDIte]
  · simp only [hq, ↓reduceDIte, map_zero]

end CoefficientMaps

end CFSG.ClassFun
