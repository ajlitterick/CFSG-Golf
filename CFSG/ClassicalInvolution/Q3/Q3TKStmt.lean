module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Q3.Q3B1

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LocalCores

@[expose] def MemberFreeSocleOuter3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ (z : Y) (L : Subgroup Y), IsClassicalMember3 L z →
      ∀ T : Subgroup Y, IsComponentOf T ⊤ → T ⊔ L = ⊤ →
        Subgroup.normalClosure (L : Set Y) = ⊤ → NonCommConnected (Q3B.conjClass L) →
          T.Normal → Subgroup.centralizer (T : Set Y) = ⊥ →
            (∀ (z' : T) (L' : Subgroup T), ¬ IsClassicalMember3 L' z') → False

@[expose] def D4OuterThree3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ (z : Y) (L : Subgroup Y), IsClassicalMember3 L z →
      ∀ T : Subgroup Y, IsComponentOf T ⊤ → T ⊔ L = ⊤ →
        Subgroup.normalClosure (L : Set Y) = ⊤ → NonCommConnected (Q3B.conjClass L) →
          T.Normal → Subgroup.centralizer (T : Set Y) = ⊥ →
            ∀ f : (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →* T,
              Function.Surjective f →
                f.ker ≤ Subgroup.center (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →
                  ∀ x ∈ L, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ T


end CFSG.ClassicalInvolution.Q3.Q3T
