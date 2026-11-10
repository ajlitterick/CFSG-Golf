module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.ActionKernel
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData
public import CFSG.CharacterTheory.PermutationCharacterOrbits

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section FixedPoints

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem fixedPointCount_semilinear [Finite F]
    (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) h =
      (Nat.card {x // semilinearAction F b m hm heven Sigma hSigma h x = x} : ℂ) := rfl


theorem mem_fixedSubfield_zpowers_iff (σ : F ≃+* F) (y : F) :
    y ∈ FixedPoints.subfield (Subgroup.zpowers σ) F ↔ σ y = y := by
  rw [CFSG.Semidihedral.FixedFieldData.mem_fixedSubfield_iff]
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro hσ a
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (F ≃+* F) y := by
      rw [Subgroup.zpowers_le]
      exact hσ
    exact hle a.2

theorem fixedPointCount_field [Finite F] {p f : ℕ} (hp : p.Prime) (hcard : Nat.card F = p ^ f)
    (σ : Sigma) :
    fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F)
        ⟨1, σ⟩ = 1 + (p : ℂ) ^ (f / orderOf σ) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hcard
  rw [fixedPointCount_semilinear, semilinearAction_mk, map_one, one_mul, card_fixed_option]
  simp only [fieldExtension_none, fieldExtension_some, Option.some.injEq, ite_true]
  have hcardA : Nat.card (Subgroup.zpowers (σ : F ≃+* F)) = orderOf σ := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
  have h := CFSG.Semidihedral.FixedFieldData.fixedSubfield_card p f F hcard
    (Subgroup.zpowers (σ : F ≃+* F))
  rw [hcardA] at h
  have hequiv : Nat.card {y : F // (σ : F ≃+* F) y = y} =
      Nat.card (FixedPoints.subfield (Subgroup.zpowers (σ : F ≃+* F)) F) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y =>
      (mem_fixedSubfield_zpowers_iff F (σ : F ≃+* F) y).symm)
  rw [hequiv, h]
  push_cast
  ring

end FixedPoints

section CyclicField

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)


end CyclicField

section ProjectiveLines

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

open CFSG.GorensteinWalter in
theorem coordinateEquiv_fieldExtension (σ : F ≃+* F) (x : Omega F) (v : Fin 2 → F)
    (hv : v ≠ 0) (hx : coordinateEquiv F x = Projectivization.mk F v hv)
    (hσv : (fun i => σ (v i)) ≠ 0) :
    coordinateEquiv F (fieldExtension F σ x) = Projectivization.mk F (fun i => σ (v i)) hσv := by
  cases x with
  | none =>
    rw [coordinateEquiv_none, psl2ProjectiveInfinity, Projectivization.mk_eq_mk_iff'] at hx
    obtain ⟨a, ha⟩ := hx
    rw [fieldExtension_none, coordinateEquiv_none, psl2ProjectiveInfinity,
      Projectivization.mk_eq_mk_iff']
    have h0 : a * v 0 = 1 := by simpa using congrFun ha 0
    have h1 : a * v 1 = 0 := by simpa using congrFun ha 1
    refine ⟨σ a, ?_⟩
    ext i
    fin_cases i
    · simp [← map_mul, h0]
    · simp [← map_mul, h1]
  | some y =>
    rw [coordinateEquiv_some, psl2AffinePoint, Projectivization.mk_eq_mk_iff'] at hx
    obtain ⟨a, ha⟩ := hx
    rw [fieldExtension_some, coordinateEquiv_some, psl2AffinePoint,
      Projectivization.mk_eq_mk_iff']
    have h0 : a * v 0 = y := by simpa using congrFun ha 0
    have h1 : a * v 1 = 1 := by simpa using congrFun ha 1
    refine ⟨σ a, ?_⟩
    ext i
    fin_cases i
    · simp [← map_mul, h0]
    · simp [← map_mul, h1]

theorem semilinearAction_projective (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m))
    (σ : Sigma) (v w : Fin 2 → F) (hv : v ≠ 0) (hw : w ≠ 0)
    (hwv : w = (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
      GeneralLinearGroup (Fin 2) F).val *ᵥ fun i => (σ : F ≃+* F) (v i)) :
    coordinateEquiv F ((⟨quotientClass F b m hm heven X j, σ⟩ :
        SemilinearExtension F b m hm heven Sigma hSigma) •
        (coordinateEquiv F).symm (Projectivization.mk F v hv)) = Projectivization.mk F w hw := by
  set C := SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val with hC
  have hσv : (fun i => (σ : F ≃+* F) (v i)) ≠ 0 := by
    intro h
    apply hv
    funext i
    have := congrFun h i
    simpa using this
  rw [semilinearExtension_smul_def, semilinearAction_mk, projAction_quotientClass,
    Equiv.Perm.mul_apply]
  change coordinateEquiv F (coordinatePGLAction F (Matrix.ProjGenLinGroup.mk C) _) = _
  rw [coordinatePGLAction_point, coordinateEquiv_fieldExtension F (σ : F ≃+* F) _ v hv
    ((coordinateEquiv F).apply_symm_apply _) hσv, Projectivization.PGL.mk_smul_mk]
  congr 1
  rw [hwv, Units.smul_def]
  rfl

end ProjectiveLines

end CFSG.Wreathed.CentralSL2
