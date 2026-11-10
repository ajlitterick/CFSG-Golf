module

public import CFSG.LocalAnalysis.GLTheoremB.UniqStatements

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def IsSCp (p : ℕ) (X B : Subgroup G) : Prop :=
  B ≤ X ∧ IsElemAbelian p B ∧ ∀ E : Subgroup G, E ≤ X → IsElemAbelian p E → B ≤ E → E = B

@[expose] noncomputable def phiOf (p : ℕ) (B : Subgroup G) (b : G) : Subgroup G :=
  sSup {L | GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L ∧
    IsStronglyLocallyOneBalanced p B b L}


@[expose] def Input20_1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    GLAPLayer p (⊤ : Subgroup X) = ⊥ → ∀ B : Subgroup X, IsSCp p ⊤ B →
      (⨆ (Y : Subgroup X) (_ : Nat.Coprime p (Nat.card Y))
        (_ : B ≤ Subgroup.normalizer (Y : Set X)), Y) = GLAPPrimeCoreOf p (⊤ : Subgroup X)

@[expose] def Input11_6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ B : Subgroup X, IsSCp p ⊤ B → GLATwoLocalRank p X ≤ pRank p B →
      ∀ Y : Subgroup X, Nat.Coprime p (Nat.card Y) → B ≤ Subgroup.normalizer (Y : Set X) →
        ∀ L : Subgroup X, GLAPComponent p ⊤ L → Y ≤ Subgroup.normalizer (L : Set X)

@[expose] def Lemma23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B : Subgroup G, IsBOneMax p B → IsSCp p ⊤ B

end CFSG.LocalAnalysis.GLTheoremB
