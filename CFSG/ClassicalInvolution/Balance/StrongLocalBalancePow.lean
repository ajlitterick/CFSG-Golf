module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceFour

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.LocalBalance

section Statement

variable {K X : Type*} [Group K] [Group X]

@[expose] def ToralActionPow (k : ℕ) (ψ : K →* X) (F : Subgroup X) : Prop :=
  ∃ P : Subgroup K, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
    ∀ f ∈ F, ∃ x ∈ P, x ^ k = 1 ∧ ∀ y : K, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)

theorem ToralActionPow.toralAction {k : ℕ} {ψ : K →* X} {F : Subgroup X}
    (h : ToralActionPow k ψ F) : ToralAction ψ F := by
  obtain ⟨P, hP, hact⟩ := h
  refine ⟨P, hP, fun f hf => ?_⟩
  obtain ⟨x, hxP, -, hxa⟩ := hact f hf
  exact ⟨x, hxP, hxa⟩

theorem ToralActionPow.mono {k k' : ℕ} (hk : k ∣ k') {ψ : K →* X} {F : Subgroup X}
    (h : ToralActionPow k ψ F) : ToralActionPow k' ψ F := by
  obtain ⟨P, hP, hact⟩ := h
  refine ⟨P, hP, fun f hf => ?_⟩
  obtain ⟨x, hxP, hxk, hxa⟩ := hact f hf
  obtain ⟨c, rfl⟩ := hk
  exact ⟨x, hxP, by rw [pow_mul, hxk, one_pow], hxa⟩


end Statement

@[expose] def StrongLocalTwoBalanceToralPowOn (k : ℕ) (t : StatedLieTag)
    (Q : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), Q n p e → IsFundTag t → StatedLieAdmissible t n p e →
    p ≠ 2 → 5 ≤ p ^ e →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K → ψ.range.Normal →
      ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
        (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) →
        ToralActionPow k ψ F → StrongConclusion ψ.range F

theorem StrongLocalTwoBalanceToralPowOn.mono {k : ℕ} {t : StatedLieTag}
    {Q Q' : ℕ → ℕ → ℕ → Prop} (h : StrongLocalTwoBalanceToralPowOn k t Q)
    (hQ : ∀ n p e, Q' n p e → Q n p e) :
    StrongLocalTwoBalanceToralPowOn k t Q' := fun n p e hp hq => h n p e hp (hQ n p e hq)


namespace Linear

open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem strongConclusion_gf_toral_two {p e n : ℕ} [Fact p.Prime] (hn : 3 ≤ n) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ e) (ψ : SL(n, GaloisField p e) →* X)
    (hker : ψ.ker ≤ Subgroup.center SL(n, GaloisField p e)) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (htoral : ToralActionPow 2 ψ F) : StrongConclusion ψ.range F := by
  obtain ⟨P, hP, hact⟩ := htoral
  refine strongConclusion_gf_split hn hp2 h5 ψ hker hnorm hcard hF2 P hP fun f hf => ?_
  obtain ⟨x, hxP, hx2, hxa⟩ := hact f hf
  refine ⟨x, hxP, hxa, 1, one_ne_zero, ?_⟩
  have hxx : x * x = 1 := by rwa [pow_two] at hx2
  have := congrArg (fun z : SL(n, GaloisField p e) =>
    (z : Matrix (Fin n) (Fin n) (GaloisField p e))) hxx
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
  rw [this]
  simp

theorem strongLocalTwoBalanceToralPowOn_PSL_two :
    StrongLocalTwoBalanceToralPowOn 2 .PSL (fun _ _ _ => True) := by
  intro n p e hp _ hfund hadm hp2 h5 X _ _ ψ hker hnorm F hcard hF2 hfaith htoral
  have : Fact p.Prime := ⟨hp⟩
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases h3 : 3 ≤ m + 1
  · exact strongConclusion_gf_toral_two h3 hp2 h5 ψ hker hnorm hcard hF2 htoral
  · exfalso
    obtain rfl : m = 1 := by omega
    have he : e ≠ 0 := by
      rintro rfl
      simp at h5
    have h4 : 4 ≤ Nat.card (GaloisField p e) := by
      rw [GaloisField.card p e he]
      omega
    exact false_of_toral_two (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2) h4
      ψ hker hcard hF2 hfaith htoral.toralAction

end Linear

end CFSG.ClassicalInvolution.Balance.StrongBalance
