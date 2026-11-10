module

public import CFSG.ClassicalInvolution.Uniform.ULieType

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly
open scoped MatrixGroups commutatorElement

theorem three_le_iff_five_le {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h3 : p ^ f ≠ 3) :
    3 ≤ p ^ f ↔ 5 ≤ p ^ f := by
  refine ⟨fun h => ?_, fun h => by omega⟩
  by_contra hlt
  have h4 : p ^ f = 4 := by omega
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h4
  have hdvd : p ∣ 4 := by
    rw [← h4]
    exact dvd_pow_self p hf
  have : p ∣ 2 ^ 2 := by simpa using hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
    ((Fact.out : p.Prime).dvd_of_dvd_pow this))


section Thm24

@[expose] def Thm4BelowU (p f : ℕ) (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ (Ω : Set (Subgroup G)),
      HypOmegaModU (.sl2 p f) Ω → classicalInvolutionOddCore G = ⊥ → (∀ K ∈ Ω, AEmpty Ω K) →
        ∀ K ∈ Ω, ∀ J ∈ Ω, (¬ ∃ g : G, conjSub g K = J) → Commutes K J

@[expose] def Thm2BelowU (p f : ℕ) (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ (Ω : Set (Subgroup G)),
      HypOmegaModU (.sl2 p f) Ω → classicalInvolutionOddCore G = ⊥ → (⨆ J ∈ Ω, J) = ⊤ → ∀ K ∈ Ω,
        (∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
          ∀ z : G, IsUniqueInvolution K z → (∃ N : Subgroup G, N.Normal ∧ IsPGroup 2 N ∧ z ∈ N) →
            K.Normal

variable {p f : ℕ} [Fact p.Prime]


end Thm24

section Thm5

@[expose] def Thm5BelowU (p f : ℕ) (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ Ω : Set (Subgroup G),
      HypOmegaModU (.sl2 p f) Ω → classicalInvolutionOddCore G = ⊥ →
        ∀ K ∈ Ω, ∀ J ∈ omegaNbr Ω K, ∀ z : G, IsUniqueInvolution K z →
          ∀ A : Subgroup G, IsElemAbelian2 A 2 → A ≤ K ⊔ J → z ∈ A → alphaOf A = ⊥

variable {p f : ℕ} [Fact p.Prime]


end Thm5

section Thm3

@[expose] def Thm3CommBelowExactU (p f : ℕ) (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → classicalInvolutionOddCore G = ⊥ →
      ∀ Ω : Set (Subgroup G), HypOmegaModU (.sl2 p f) Ω → ∀ K ∈ Ω, ¬ AEmpty Ω K →
        T3.aStar Ω K = T3.vStar Ω K ∧
          ∀ L ∈ Ω, L ∉ T3.vStar Ω K → ∀ M ∈ T3.vStar Ω K, ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M

@[expose] def Thm3LieBelowExactU (p f : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → classicalInvolutionOddCore G = ⊥ →
      ∀ Ω : Set (Subgroup G), HypOmegaModU (.sl2 p f) Ω → ∀ K ∈ Ω, ¬ AEmpty Ω K →
        SectionLieTypeU p f Ω (omegaGen (T3.aStar Ω K)) .G2 0

@[expose] def Thm3TypedBelowExactU (p f : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  Thm3CommBelowExactU p f n ∧ Thm3LieBelowExactU p f n


end Thm3

end CFSG.ClassicalInvolution.Uniform
