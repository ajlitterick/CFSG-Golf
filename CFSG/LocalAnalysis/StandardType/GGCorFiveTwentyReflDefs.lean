module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTorusReflBridge (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      ∀ (β : MulAut L') (β' : MulAut R), (∀ l : L', β' (ψ l) = ψ (β l)) →
        (∀ a ∈ A, β * a * β⁻¹ ∈ A) →
        (∀ a ∈ A, β ^ (p - 1) * a * (β ^ (p - 1))⁻¹ = a) →
        Nat.card {a : A // β * (a : MulAut L') * β⁻¹ = a} * p = Nat.card A →
        ∃ n : L', (∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧
            ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
          ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ = β * a * β⁻¹


end CFSG.StandardType

end
