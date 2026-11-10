module

public import CFSG.LargeExtraspecial.S4Restrict
public import CFSG.LargeExtraspecial.S4Span

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] def RmodN (g : G) (t : S.O) : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t) where
  carrier := {e | ∃ x ∈ Rbar S g t, ∀ v : Vt S g t, ((e v : Vt S g t) : S.Qt) =
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v}
  mul_mem' := by
    rintro e f ⟨x, hx, hex⟩ ⟨y, hy, hfy⟩
    refine ⟨x * y, mul_mem hx hy, fun v => ?_⟩
    rw [LinearEquiv.mul_apply, hex, hfy]
    rfl
  one_mem' := ⟨1, one_mem _, fun v => rfl⟩
  inv_mem' := by
    rintro e ⟨x, hx, hex⟩
    refine ⟨x⁻¹, inv_mem hx, fun v => ?_⟩
    have h1 := hex (e⁻¹ v)
    rw [show e (e⁻¹ v) = v from e.apply_symm_apply v] at h1
    rw [h1, inv_apply_apply_O]

variable (S) in
@[expose] def LmodN (g : G) (t : S.O) : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t) where
  carrier := {e | ∃ x ∈ S.Lbar g, ∀ v : Vt S g t, ((e v : Vt S g t) : S.Qt) =
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v}
  mul_mem' := by
    rintro e f ⟨x, hx, hex⟩ ⟨y, hy, hfy⟩
    refine ⟨x * y, mul_mem hx hy, fun v => ?_⟩
    rw [LinearEquiv.mul_apply, hex, hfy]
    rfl
  one_mem' := ⟨1, one_mem _, fun v => rfl⟩
  inv_mem' := by
    rintro e ⟨x, hx, hex⟩
    refine ⟨x⁻¹, inv_mem hx, fun v => ?_⟩
    have h1 := hex (e⁻¹ v)
    rw [show e (e⁻¹ v) = v from e.apply_symm_apply v] at h1
    rw [h1, inv_apply_apply_O]

theorem mem_RmodN {t : S.O} {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t} :
    e ∈ RmodN S g t ↔ ∃ x ∈ Rbar S g t, ∀ v : Vt S g t, ((e v : Vt S g t) : S.Qt) =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
  Iff.rfl

theorem mem_LmodN {t : S.O} {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t} :
    e ∈ LmodN S g t ↔ ∃ x ∈ S.Lbar g, ∀ v : Vt S g t, ((e v : Vt S g t) : S.Qt) =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
  Iff.rfl

@[expose] noncomputable def resV (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) :
    Rbar S g t →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t) :=
  restrictHom (S.O.subtype.comp (Rbar S g t).subtype) (Vt S g t)
    (fun x _ hu => apply_mem_Vt_of_mem_Rbar haQ x.2 hu)

theorem coe_resV_apply (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (x : Rbar S g t)
    (v : Vt S g t) :
    ((resV haQ t x v : Vt S g t) : S.Qt) = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
  rfl

theorem range_resV (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) :
    (resV haQ t).range = RmodN S g t := by
  ext e
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, fun v => rfl⟩
  · rintro ⟨x, hx, hex⟩
    exact ⟨⟨x, hx⟩, LinearEquiv.ext fun v => Subtype.ext (hex v).symm⟩

theorem resV_eq_one_iff (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (x : Rbar S g t) :
    resV haQ t x = 1 ↔ (x : S.O) ∈ Nbar S g t := by
  have := restrictHom_eq_one_iff (S.O.subtype.comp (Rbar S g t).subtype) (Vt S g t)
    (fun x _ hu => apply_mem_Vt_of_mem_Rbar haQ x.2 hu) x
  exact this.trans ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem LmodN_le_RmodN {t : S.O} (ht : t ∈ S.Lbar g) : LmodN S g t ≤ RmodN S g t := by
  rintro e ⟨x, hx, hex⟩
  exact ⟨x, Lbar_le_Rbar ht hx, hex⟩

@[expose] noncomputable def resL (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g) :
    S.Lbar g →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t) :=
  restrictHom (S.O.subtype.comp (S.Lbar g).subtype) (Vt S g t)
    (fun x _ hu => apply_mem_Vt_of_mem_Rbar haQ (Lbar_le_Rbar ht x.2) hu)

theorem range_resL (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g) :
    (resL haQ ht).range = LmodN S g t := by
  ext e
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, fun v => rfl⟩
  · rintro ⟨x, hx, hex⟩
    exact ⟨⟨x, hx⟩, LinearEquiv.ext fun v => Subtype.ext (hex v).symm⟩


end CFSG.LargeExtraspecial.S4
