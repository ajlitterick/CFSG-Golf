module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutSemi
public import CFSG.LieType.Universal.Spin.Generation.Eichler

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped Matrix

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

theorem eichler_smul_left {Q : QuadraticForm F V} {u w : V} (c : F) (hu : Q u = 0)
    (huw : polar Q u w = 0) : eichler Q (c • u) w = eichler Q u (c • w) := by
  have h1 : Q (c • u) = 0 := by rw [QuadraticMap.map_smul, hu, smul_zero]
  have h2 : polar Q (c • u) w = 0 := by rw [polar_smul_left, huw, smul_zero]
  have h3 : polar Q u (c • w) = 0 := by rw [polar_smul_right, huw, smul_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply h1 h2, eichler_apply hu h3]
  simp only [polar_smul_right, QuadraticMap.map_smul, smul_eq_mul, smul_smul]
  module

section Sign

variable {Q : QuadraticForm F V} {p : ℕ} [Fact p.Prime]

theorem hom_eq_of_spinAction_eq (hp2 : p ≠ 2) {W : Type} [AddCommGroup W] [Module F W]
    (hker : ∀ x ∈ (spinAction Q).ker, x * x = 1)
    (f g : Multiplicative W →* spinGroup Q) (hW : ∀ w : W, p • w = 0)
    (h : ∀ w, spinAction Q (f w) = spinAction Q (g w)) : f = g := by
  let z : Multiplicative W →* spinGroup Q :=
    MonoidHom.mk' (fun c => (f c)⁻¹ * g c) (fun c d => by
      have hz : (f c)⁻¹ * g c ∈ Subgroup.center (spinGroup Q) :=
        ker_spinAction_le_center Q (by
          rw [MonoidHom.mem_ker, map_mul, map_inv, h c, inv_mul_cancel])
      have hc := Subgroup.mem_center_iff.mp hz (f d)⁻¹
      calc (f (c * d))⁻¹ * g (c * d)
          = (f d)⁻¹ * (((f c)⁻¹ * g c) * g d) := by
            rw [map_mul, map_mul]
            group
        _ = ((f c)⁻¹ * g c) * ((f d)⁻¹ * g d) := by rw [← mul_assoc, hc]; group)
  have hz1 : ∀ c, z c = 1 := fun c => by
    have hker' : z c * z c = 1 := by
      apply hker
      rw [MonoidHom.mem_ker]
      change spinAction Q ((f c)⁻¹ * g c) = 1
      rw [map_mul, map_inv, h c, inv_mul_cancel]
    have hp : z c ^ p = 1 := by
      rw [← map_pow]
      have : c ^ p = 1 := by
        rw [← ofAdd_toAdd c, ← ofAdd_nsmul, hW, ofAdd_zero]
      rw [this, map_one]
    obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
    calc z c = z c ^ p := by rw [hk, pow_succ, pow_mul, _root_.sq, hker', one_pow, one_mul]
      _ = 1 := hp
  refine MonoidHom.ext fun c => ?_
  have := hz1 c
  change (f c)⁻¹ * g c = 1 at this
  exact inv_mul_eq_one.mp this

end Sign

section Plane

variable {Q : QuadraticForm F V} {e f : V}


end Plane

section Roots

variable {Q : QuadraticForm F V} {p : ℕ} [Fact p.Prime] [CharP F p] {m : ℕ}

omit [Fact p.Prime] in
theorem nsmul_eq_zero_of_charP (w : F) : p • w = 0 := by
  rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

theorem IsConj.longRoot_eq (hp2 : p ≠ 2) (hker : ∀ x ∈ (spinAction Q).ker, x * x = 1)
    (Fr : HypFrame Q m) {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q} (h : IsConj α g)
    (lam : Fin m → Bool → F) (sw : Fin m → Bool → Bool)
    (hg : ∀ i s, g (Fr.vec i s) = lam i s • Fr.vec i (sw i s))
    {i j : Fin m} (hij : i ≠ j) (s t : Bool) (c : F) :
    α (Fr.longRoot hij s t (.ofAdd c)) =
      Fr.longRoot hij (sw i s) (sw j t)
        (.ofAdd (lam j t * ((g.μ : F)⁻¹ * (lam i s * g.φ c)))) := by
  let κ : F := lam j t * ((g.μ : F)⁻¹ * lam i s)
  let ψ : F →+ F := (AddMonoidHom.mulLeft κ).comp (g.φ : F →+* F).toAddMonoidHom
  let f₁ : Multiplicative F →* spinGroup Q := (α : spinGroup Q →* spinGroup Q).comp
    (Fr.longRoot hij s t)
  let f₂ : Multiplicative F →* spinGroup Q :=
    (Fr.longRoot hij (sw i s) (sw j t)).comp (AddMonoidHom.toMultiplicative ψ)
  have key : ∀ c' : F, spinAction Q (f₁ (.ofAdd c')) = spinAction Q (f₂ (.ofAdd c')) := fun c' => by
    have hu : Q (Fr.vec j t) = 0 := Fr.map_vec j t
    have huw : polar Q (Fr.vec j t) (c' • Fr.vec i s) = 0 := by
      rw [polar_smul_right, Fr.polar_vec_of_ne hij.symm, smul_zero]
    have h1 := h.spinAction_eq_eichler (Fr.spinAction_longRoot_eq_eichler hij s t c') hu huw
    change spinAction Q (α (Fr.longRoot hij s t (.ofAdd c'))) =
      spinAction Q (Fr.longRoot hij (sw i s) (sw j t) (.ofAdd (ψ c')))
    rw [h1, Fr.spinAction_longRoot_eq_eichler, g.map_smul, hg, hg]
    have hu' : Q (Fr.vec j (sw j t)) = 0 := Fr.map_vec j _
    have huw' : polar Q (Fr.vec j (sw j t))
        (((g.μ : F)⁻¹) • (g.φ c' • (lam i s • Fr.vec i (sw i s)))) = 0 := by
      simp only [polar_smul_right, Fr.polar_vec_of_ne hij.symm, smul_zero]
    rw [eichler_smul_left _ hu' huw']
    change eichler Q (Fr.vec j (sw j t)) (lam j t • (((g.μ : F)⁻¹) • (g.φ c' •
      (lam i s • Fr.vec i (sw i s))))) =
        eichler Q (Fr.vec j (sw j t)) ((κ * g.φ c') • Fr.vec i (sw i s))
    congr 1
    simp only [smul_smul, κ]
    congr 1
    ring
  have hfg : f₁ = f₂ := hom_eq_of_spinAction_eq hp2 hker f₁ f₂ nsmul_eq_zero_of_charP
    (fun w => key (Multiplicative.toAdd w))
  have hc := congrArg (fun f : Multiplicative F →* spinGroup Q => f (.ofAdd c)) hfg
  have e : AddMonoidHom.toMultiplicative ψ (Multiplicative.ofAdd c) =
      Multiplicative.ofAdd (lam j t * ((g.μ : F)⁻¹ * (lam i s * g.φ c))) := by
    change Multiplicative.ofAdd (ψ c) = _
    congr 1
    change κ * g.φ c = _
    simp only [κ]
    ring
  calc α (Fr.longRoot hij s t (.ofAdd c)) = f₁ (.ofAdd c) := rfl
    _ = f₂ (.ofAdd c) := hc
    _ = Fr.longRoot hij (sw i s) (sw j t) (AddMonoidHom.toMultiplicative ψ (.ofAdd c)) := rfl
    _ = _ := by rw [e]

theorem IsConj.shortRoot_eq (hp2 : p ≠ 2) (hker : ∀ x ∈ (spinAction Q).ker, x * x = 1)
    (Fr : OddFrame Q m) {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q} (h : IsConj α g)
    (lam : Fin m → Bool → F) (sw : Fin m → Bool → Bool)
    (hg : ∀ i s, g (Fr.vec i s) = lam i s • Fr.vec i (sw i s)) (ζ : F)
    (hz : g Fr.z = ζ • Fr.z) (i : Fin m) (s : Bool) (c : F) :
    α (Fr.shortRoot i s (.ofAdd c)) =
      Fr.shortRoot i (sw i s) (.ofAdd (lam i s * ((g.μ : F)⁻¹ * (ζ * g.φ c)))) := by
  let κ : F := lam i s * ((g.μ : F)⁻¹ * ζ)
  let ψ : F →+ F := (AddMonoidHom.mulLeft κ).comp (g.φ : F →+* F).toAddMonoidHom
  let f₁ : Multiplicative F →* spinGroup Q := (α : spinGroup Q →* spinGroup Q).comp
    (Fr.shortRoot i s)
  let f₂ : Multiplicative F →* spinGroup Q :=
    (Fr.shortRoot i (sw i s)).comp (AddMonoidHom.toMultiplicative ψ)
  have key : ∀ c' : F, spinAction Q (f₁ (.ofAdd c')) = spinAction Q (f₂ (.ofAdd c')) := fun c' => by
    have hu : Q (Fr.vec i s) = 0 := Fr.map_vec i s
    have huw : polar Q (Fr.vec i s) (c' • Fr.z) = 0 := by
      rw [polar_smul_right, Fr.polar_vec_z, smul_zero]
    have h1 := h.spinAction_eq_eichler (Fr.spinAction_shortRoot_eq_eichler i s c') hu huw
    change spinAction Q (α (Fr.shortRoot i s (.ofAdd c'))) =
      spinAction Q (Fr.shortRoot i (sw i s) (.ofAdd (ψ c')))
    rw [h1, Fr.spinAction_shortRoot_eq_eichler, g.map_smul, hg, hz]
    have hu' : Q (Fr.vec i (sw i s)) = 0 := Fr.map_vec i _
    have huw' : polar Q (Fr.vec i (sw i s))
        (((g.μ : F)⁻¹) • (g.φ c' • (ζ • Fr.z))) = 0 := by
      simp only [polar_smul_right, Fr.polar_vec_z, smul_zero]
    rw [eichler_smul_left _ hu' huw']
    change eichler Q (Fr.vec i (sw i s)) (lam i s • (((g.μ : F)⁻¹) • (g.φ c' • (ζ • Fr.z)))) =
        eichler Q (Fr.vec i (sw i s)) ((κ * g.φ c') • Fr.z)
    congr 1
    simp only [smul_smul, κ]
    congr 1
    ring
  have hfg : f₁ = f₂ := hom_eq_of_spinAction_eq hp2 hker f₁ f₂ nsmul_eq_zero_of_charP
    (fun w => key (Multiplicative.toAdd w))
  have hc := congrArg (fun f : Multiplicative F →* spinGroup Q => f (.ofAdd c)) hfg
  have e : AddMonoidHom.toMultiplicative ψ (Multiplicative.ofAdd c) =
      Multiplicative.ofAdd (lam i s * ((g.μ : F)⁻¹ * (ζ * g.φ c))) := by
    change Multiplicative.ofAdd (ψ c) = _
    congr 1
    change κ * g.φ c = _
    simp only [κ]
    ring
  calc α (Fr.shortRoot i s (.ofAdd c)) = f₁ (.ofAdd c) := rfl
    _ = f₂ (.ofAdd c) := hc
    _ = Fr.shortRoot i (sw i s) (AddMonoidHom.toMultiplicative ψ (.ofAdd c)) := rfl
    _ = _ := by rw [e]

end Roots

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
