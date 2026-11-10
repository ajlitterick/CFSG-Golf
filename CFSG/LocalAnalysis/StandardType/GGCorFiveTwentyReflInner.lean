module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticLift
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace ReflInner

section Lift

variable {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R}

theorem conj_eq_conj_of_map_eq (hker : ψ.ker ≤ Subgroup.center L') {x y : L'}
    (h : ψ x = ψ y) : MulAut.conj x = MulAut.conj y := by
  have hk : x⁻¹ * y ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hc := Subgroup.mem_center_iff.mp (hker hk)
  ext g
  rw [MulAut.conj_apply, MulAut.conj_apply]
  calc x * g * x⁻¹ = x * (g * (x⁻¹ * y)) * (x⁻¹ * y)⁻¹ * x⁻¹ := by group
    _ = x * ((x⁻¹ * y) * g) * (x⁻¹ * y)⁻¹ * x⁻¹ := by rw [hc g]
    _ = y * g * y⁻¹ := by group

theorem map_eq_of_conj_eq (hψ : Function.Surjective ψ) (hR : Subgroup.center R = ⊥) {x y : L'}
    (h : MulAut.conj x = MulAut.conj y) : ψ x = ψ y := by
  have hc : ∀ g : L', g * (x⁻¹ * y) = (x⁻¹ * y) * g := by
    intro g
    have e : x * g * x⁻¹ = y * g * y⁻¹ := by
      have := congrArg (fun φ : MulAut L' => φ g) h
      simpa only [MulAut.conj_apply] using this
    calc g * (x⁻¹ * y) = x⁻¹ * (x * g * x⁻¹) * y := by group
      _ = x⁻¹ * (y * g * y⁻¹) * y := by rw [e]
      _ = x⁻¹ * y * g := by group
  have hz : ψ (x⁻¹ * y) ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨g, rfl⟩ := hψ r
    rw [← map_mul, ← map_mul, hc g]
  rw [hR, Subgroup.mem_bot, map_mul, map_inv, inv_mul_eq_one] at hz
  exact hz

variable (ψ) in
@[expose] noncomputable def liftConj (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') : R →* MulAut L' where
  toFun e := MulAut.conj (Function.surjInv hψ e)
  map_one' := (conj_eq_conj_of_map_eq hker (y := 1)
    (by rw [Function.surjInv_eq hψ, map_one])).trans (map_one _)
  map_mul' e₁ e₂ := (conj_eq_conj_of_map_eq hker
    (y := Function.surjInv hψ e₁ * Function.surjInv hψ e₂)
    (by rw [map_mul, Function.surjInv_eq hψ, Function.surjInv_eq hψ,
      Function.surjInv_eq hψ])).trans (map_mul _ _ _)

theorem liftConj_eq (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') {e : R}
    {x : L'} (hx : ψ x = e) : liftConj ψ hψ hker e = MulAut.conj x :=
  conj_eq_conj_of_map_eq hker (by rw [Function.surjInv_eq hψ, hx])

theorem map_liftConj_apply (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (e : R) (l : L') : ψ (liftConj ψ hψ hker e l) = e * ψ l * e⁻¹ := by
  obtain ⟨x, rfl⟩ := hψ e
  rw [liftConj_eq hψ hker rfl, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem liftConj_injective (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hR : Subgroup.center R = ⊥) : Function.Injective (liftConj ψ hψ hker) := by
  intro e₁ e₂ h
  obtain ⟨x, rfl⟩ := hψ e₁
  obtain ⟨y, rfl⟩ := hψ e₂
  rw [liftConj_eq hψ hker rfl, liftConj_eq hψ hker rfl] at h
  exact map_eq_of_conj_eq hψ hR h


end Lift

theorem pow_eq_one_of_zmod {p k : ℕ} (f : Fin k → Multiplicative (ZMod p)) : f ^ p = 1 := by
  funext i
  rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (f i), ← ofAdd_nsmul, nsmul_eq_mul,
    ZMod.natCast_self, zero_mul, ofAdd_zero]

section Conj


end Conj

section Fixed


end Fixed

end ReflInner


end CFSG.StandardType

end
