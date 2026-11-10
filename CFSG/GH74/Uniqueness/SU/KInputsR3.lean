module

public import CFSG.GH74.Uniqueness.SU.KInputs2
public import CFSG.GH74.Uniqueness.SU.SU5Main

public section

namespace CFSG.GH74.Uniqueness.SU.K

open Subgroup CFSG.Blueprint

@[expose] def KI1r3 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SU0.GHGroup H → pPrimeCore 2 H = ⊥ →
    Open.twoRank H = 3 → center H = ⊥ →
    ∀ (T : Sylow 2 H) (x : H), x ∈ (T : Subgroup H) → orderOf x = 2 →
      Open.pRank 2 (centralizer ({x} : Set H)) = 2 →
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel ↥(generalizedFitting H) .PSL 2 p f ∧
          IsPGL2 ↥(generalizedFitting H ⊔ zpowers x) p f


@[expose] def KI5b : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) → center K ≠ ⊥ →
    Nonempty ((K ⧸ center K) ≃* CFSG.Theory.Comparator.SzModel 1) →
      (∀ (P : Sylow 2 K), ∀ g ∈ (P : Subgroup K), g ^ 2 ∈ center K → g ^ 2 = 1) ∧
      (∀ (P : Sylow 2 K), ∀ g ∈ (P : Subgroup K), ∀ h ∈ (P : Subgroup K),
        g ^ 2 ∈ center K → h ^ 2 ∈ center K → g * h = h * g)


@[expose] def KI7b9 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsTwoAlt X 9 → 4 ≤ Open.twoRank X


end CFSG.GH74.Uniqueness.SU.K
