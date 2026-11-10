module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHBase

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def T5BaseAt (p f : ℕ) [Fact p.Prime] (t : StatedLieTag) (k e : ℕ) (P : Prop → Prop) :
    Prop :=
  p ≠ 2 → 5 ≤ p ^ f → IsFundTag t → StatedLieAdmissible t k p e →
    (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) →
      ∀ (H : Type) [Group H] [Finite H] (ψ : (modelUniv t k p e Fact.out).K →* H),
        ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K →
        ∀ R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D,
          ∀ R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D,
            Nonempty (↥(R.map ψ) ≃* SL(2, GaloisField p f)) →
            Nonempty (↥(R'.map ψ) ≃* SL(2, GaloisField p f)) →
            R.map ψ ≠ R'.map ψ → Commutes (R.map ψ) (R'.map ψ) →
            ∀ z : H, IsUniqueInvolution (R.map ψ) z → P (z ∈ R'.map ψ) →
              ∀ A : Subgroup H, IsElemAbelian2 A 2 → A ≤ R.map ψ ⊔ R'.map ψ → z ∈ A →
                (∀ a ∈ A, a ≠ 1 → ¬ ∀ x ∈ ψ.range, a * x = x * a) →
                  alphaOf (inducedImage ψ.range A) = ⊥


end CFSG.ClassicalInvolution.Asc77
