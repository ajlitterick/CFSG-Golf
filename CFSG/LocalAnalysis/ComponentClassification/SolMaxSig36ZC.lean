module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36E

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv


@[expose] def SignalizerCaseOneStrongClosureElevenInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)) (E : Subgroup X) (D : Finset (Fin 11)),
    Sig36 X t J 11 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      ∀ a ∈ Q, ∀ g : X, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ Q


end CFSG.ComponentClassification.SolMax
