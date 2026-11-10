module

public import CFSG.ClassicalInvolution.Balance.BootstrapAlphaConst
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTriple
import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.Balance.BootstrapDelta

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Open (IsElemAbelian signalizerFunctorEk)
open scoped commutatorElement

section Statement

variable {K X : Type*} [Group K] [Group X]

@[expose] def ToralAction (ψ : K →* X) (F : Subgroup X) : Prop :=
  ∃ P : Subgroup K, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
    ∀ f ∈ F, ∃ x ∈ P, ∀ y : K, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)

theorem ToralAction.mono {ψ : K →* X} {F F' : Subgroup X} (h : ToralAction ψ F) (hle : F' ≤ F) :
    ToralAction ψ F' := by
  obtain ⟨P, hP, hact⟩ := h
  exact ⟨P, hP, fun f hf => hact f (hle hf)⟩

@[expose] def StrongConclusion (L F : Subgroup X) : Prop :=
  (∀ d ∈ deltaCore F, ∀ x ∈ L, d * x = x * d) ∧
    ∀ f ∈ F, f ≠ 1 → ∀ d ∈ involutionOddCore f, ∀ g ∈ F, ∀ x ∈ L,
      d * g * x * (d * g)⁻¹ = g * d * x * (g * d)⁻¹

end Statement

@[expose] def StrongLocalTwoBalanceToralOn (t : StatedLieTag) (Q : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), Q n p e → IsFundTag t → StatedLieAdmissible t n p e →
    p ≠ 2 → 5 ≤ p ^ e →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K → ψ.range.Normal →
      ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
        (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) →
        ToralAction ψ F → StrongConclusion ψ.range F

theorem StrongLocalTwoBalanceToralOn.mono {t : StatedLieTag} {Q Q' : ℕ → ℕ → ℕ → Prop}
    (h : StrongLocalTwoBalanceToralOn t Q) (hQ : ∀ n p e, Q' n p e → Q n p e) :
    StrongLocalTwoBalanceToralOn t Q' := fun n p e hp hq => h n p e hp (hQ n p e hq)


section Aux

variable {K : Type*} [Group K]

theorem aux_central_commutator (c₁ c₂ g₁ g₂ : K) (h1 : ∀ x, x * c₁ = c₁ * x)
    (h2 : ∀ x, x * c₂ = c₂ * x) :
    (c₁ * g₁) * (c₂ * g₂) * (c₁ * g₁)⁻¹ * (c₂ * g₂)⁻¹ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by
  have f1 : c₁ * g₁ * c₂ * g₂ = c₁ * c₂ * (g₁ * g₂) := by
    rw [mul_assoc c₁ g₁ c₂, h2 g₁]; group
  have f2 : c₂ * g₂ * c₁ * g₁ = c₁ * c₂ * (g₂ * g₁) := by
    rw [mul_assoc c₂ g₂ c₁, h1 g₂, ← mul_assoc c₂ c₁, h1 c₂]; group
  have hu : ∀ x, (c₁ * c₂) * x * (c₁ * c₂)⁻¹ = x := fun x => by
    have : x * (c₁ * c₂) = (c₁ * c₂) * x := by
      rw [← mul_assoc, h1 x, mul_assoc, h2 x, mul_assoc]
    rw [← this, mul_inv_cancel_right]
  calc (c₁ * g₁) * (c₂ * g₂) * (c₁ * g₁)⁻¹ * (c₂ * g₂)⁻¹
      = (c₁ * g₁ * c₂ * g₂) * (c₂ * g₂ * c₁ * g₁)⁻¹ := by group
    _ = (c₁ * c₂ * (g₁ * g₂)) * (c₁ * c₂ * (g₂ * g₁))⁻¹ := by rw [f1, f2]
    _ = (c₁ * c₂) * ((g₁ * g₂) * (g₂ * g₁)⁻¹) * (c₁ * c₂)⁻¹ := by group
    _ = (g₁ * g₂) * (g₂ * g₁)⁻¹ := hu _
    _ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by group

theorem commute_of_perfect_of_commutator_mem_center {r : K} {R : Subgroup K} (hR : R ≤ ⁅R, R⁆)
    (h : ∀ s ∈ R, r * s * r⁻¹ * s⁻¹ ∈ Subgroup.center K) : ∀ s ∈ R, r * s = s * r := by
  have hC : ⁅R, R⁆ ≤ Subgroup.centralizer ({r} : Set K) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
    obtain ⟨c₁, hc₁⟩ : ∃ c, c = r * g₁ * r⁻¹ * g₁⁻¹ := ⟨_, rfl⟩
    obtain ⟨c₂, hc₂⟩ : ∃ c, c = r * g₂ * r⁻¹ * g₂⁻¹ := ⟨_, rfl⟩
    have h1 : ∀ x, x * c₁ = c₁ * x := hc₁ ▸ Subgroup.mem_center_iff.mp (h g₁ hg₁)
    have h2 : ∀ x, x * c₂ = c₂ * x := hc₂ ▸ Subgroup.mem_center_iff.mp (h g₂ hg₂)
    have e1 : r * g₁ * r⁻¹ = c₁ * g₁ := by rw [hc₁]; simp
    have e2 : r * g₂ * r⁻¹ = c₂ * g₂ := by rw [hc₂]; simp
    have e3 : r * g₁⁻¹ * r⁻¹ = (c₁ * g₁)⁻¹ := by rw [← e1]; group
    have e4 : r * g₂⁻¹ * r⁻¹ = (c₂ * g₂)⁻¹ := by rw [← e2]; group
    have key : r * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * r⁻¹ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by
      calc r * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * r⁻¹
          = (r * g₁ * r⁻¹) * (r * g₂ * r⁻¹) * (r * g₁⁻¹ * r⁻¹) * (r * g₂⁻¹ * r⁻¹) := by group
        _ = (c₁ * g₁) * (c₂ * g₂) * (c₁ * g₁)⁻¹ * (c₂ * g₂)⁻¹ := by rw [e1, e2, e3, e4]
        _ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := aux_central_commutator _ _ _ _ h1 h2
    have h3 : r * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * r := by
      have := congrArg (· * r) key
      simpa [mul_assoc] using this
    exact h3.symm
  intro s hs
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hC (hR hs))).symm

end Aux

section Frame


end Frame


section ModelLevel

variable {X : Type} [Group X] [Finite X]

theorem odd_orderOf_of_mem_involutionOddCore {f d : X} (hd : d ∈ involutionOddCore f) :
    Odd (orderOf d) :=
  (odd_card_oddCoreIn (Subgroup.centralizer ({f} : Set X))).of_dvd_nat
    (Subgroup.orderOf_dvd_natCard _ hd)


end ModelLevel

end CFSG.ClassicalInvolution.Balance.StrongBalance
