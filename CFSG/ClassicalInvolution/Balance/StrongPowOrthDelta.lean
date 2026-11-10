module

public import CFSG.ClassicalInvolution.Balance.StrongPowOrthSide
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagDefs

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance (deltaCore)

@[expose] def OrthGenAniso : Prop :=
  ∀ (F V : Type) [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), (polarBilin Q).Nondegenerate → Odd (Nat.card F) → 5 ≤ Nat.card F →
    7 ≤ Module.finrank F V → ∀ t₁ t₂ : V ≃ₗ[F] V,
      t₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q → t₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q →
      t₁ * t₁ = 1 → t₂ * t₂ = 1 → t₁ * t₂ = t₂ * t₁ →
      (∀ x : V, ∀ ε δ : F, t₁ x = ε • x → t₂ x = δ • x → Q x = 0 → x = 0) →
      ∀ H : Subgroup (V ≃ₗ[F] V),
        (∀ ε : F, ε * ε = 1 → elemOn Q (eigenSub t₁ ε) ≤ H) →
        (∀ δ : F, δ * δ = 1 → elemOn Q (eigenSub t₂ δ) ≤ H) →
        (∀ c : F, c * c = 1 → elemOn Q (eigenSub (t₁ * t₂) c) ≤ H) →
        elementaryGroup Q ≤ H

section Delta

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem eigenvalue_sq_eq_one {t : V ≃ₗ[F] V} (ht : t * t = 1) {x : V} (hx : x ≠ 0) {ε : F}
    (h : t x = ε • x) : ε * ε = 1 := by
  have h1 : t (t x) = x := by
    have := congrArg (fun g : V ≃ₗ[F] V => g x) ht
    simpa using this
  rw [h, LinearEquiv.map_smul, h, smul_smul] at h1
  by_contra hne
  apply hx
  have : (ε * ε - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
  exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)


end Delta

end CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
