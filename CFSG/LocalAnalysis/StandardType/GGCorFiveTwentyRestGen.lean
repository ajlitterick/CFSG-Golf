module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def ggTorusPseudoReflSet (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) :
    Set (MulAut ↥A) :=
  {φ | ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
    GGTorusWeylElt p A n ∧ φ = ggConjAut A hn ∧ GGIsPseudoReflection p φ}

@[expose] def GGTorusPseudoReflGen (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤
        Subgroup.closure (ggTorusPseudoReflSet p A)

@[expose] def GGTorusWeylNormInner (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      ∀ φ ∈ Subgroup.normalizer
        (ggAutomizer (MulAut.conj : L' →* MulAut L').range A : Set (MulAut ↥A)),
        ∃ w ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
          ∀ v ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, φ * v * φ⁻¹ = w * v * w⁻¹


section Transport


end Transport


end CFSG.StandardType

end
