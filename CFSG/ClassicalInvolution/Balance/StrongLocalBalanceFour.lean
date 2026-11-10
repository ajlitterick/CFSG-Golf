module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearToral

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance

section Statement

variable {K X : Type*} [Group K] [Group X]

@[expose] def ToralActionFour (ψ : K →* X) (F : Subgroup X) : Prop :=
  ∃ P : Subgroup K, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
    ∀ f ∈ F, ∃ x ∈ P, x ^ 4 = 1 ∧ ∀ y : K, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)

theorem ToralActionFour.toralAction {ψ : K →* X} {F : Subgroup X} (h : ToralActionFour ψ F) :
    ToralAction ψ F := by
  obtain ⟨P, hP, hact⟩ := h
  refine ⟨P, hP, fun f hf => ?_⟩
  obtain ⟨x, hxP, -, hxa⟩ := hact f hf
  exact ⟨x, hxP, hxa⟩

end Statement

@[expose] def StrongLocalTwoBalanceToralFourOn (t : StatedLieTag) (Q : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), Q n p e → IsFundTag t → StatedLieAdmissible t n p e →
    p ≠ 2 → 5 ≤ p ^ e →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K → ψ.range.Normal →
      ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
        (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) →
        ToralActionFour ψ F → StrongConclusion ψ.range F

theorem StrongLocalTwoBalanceToralFourOn.mono {t : StatedLieTag} {Q Q' : ℕ → ℕ → ℕ → Prop}
    (h : StrongLocalTwoBalanceToralFourOn t Q) (hQ : ∀ n p e, Q' n p e → Q n p e) :
    StrongLocalTwoBalanceToralFourOn t Q' := fun n p e hp hq => h n p e hp (hQ n p e hq)


namespace Linear

open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]


theorem isSquare_neg_one_galoisField {p e : ℕ} [Fact p.Prime] (he : e ≠ 0)
    (hq : p ^ e % 4 = 1) : IsSquare (-1 : GaloisField p e) := by
  have : Fintype (GaloisField p e) := Fintype.ofFinite _
  rw [FiniteField.isSquare_neg_one_iff, Fintype.card_eq_nat_card, GaloisField.card p e he, hq]
  norm_num


end Linear

end CFSG.ClassicalInvolution.Balance.StrongBalance
