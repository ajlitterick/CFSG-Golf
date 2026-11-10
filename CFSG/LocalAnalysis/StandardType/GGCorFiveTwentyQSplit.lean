module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGLabQFour (_p : ℕ) (lab : LargeEvenLabel) : Prop := 2 ≤ lab.n

@[expose] def GGLabQTwo (_p : ℕ) (lab : LargeEvenLabel) : Prop := lab.n < 2

@[expose] def GGLabNbrOk (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  2 ≤ lab.n ∨ (lab.tag = .A ∧ lab.n = 1 ∧ p = 3 ∧ 5 ≤ lab.rank)

@[expose] def GGNbrLabelsOk {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (D J : Subgroup G) : Prop :=
  ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGInnerDiagOnLabel GGLabNbrOk p Bs K

@[expose] def GGCorFiveTwentyInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel S p Bs L →
      Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGCorFiveTwentyInputQTwo : Prop :=
  GGCorFiveTwentyInputOn GGLabQTwo


@[expose] def GGCorFiveTwentyQFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)


@[expose] def GGLabPhiOneTwo (p : ℕ) (lab : LargeEvenLabel) : Prop := p ∣ 4 ^ lab.n - 1

@[expose] def GGCorFiveTwentyWeylDom {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) : Prop :=
  GGScalarsPmOne Bs ∧ GGReflGenerated p (ggAutomizer L Bs) ∧
    GGInnerDiagOnLabel GGLabPhiOneTwo p Bs L ∧
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) ∧ GGInnerDiagOnLabel GGLabPhiOneTwo p Bs K

@[expose] def GGCorFiveTwentyQFourNonWeylInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → ¬ GGCorFiveTwentyWeylDom p B Bs x L D J →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGCorFiveTwentyQFourWeylInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDom p B Bs x L D J →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

theorem ggCorFiveTwentyQFourInput_of_weyl (hN : GGCorFiveTwentyQFourNonWeylInput)
    (hW : GGCorFiveTwentyQFourWeylInput) : GGCorFiveTwentyQFourInput := by
  intro G _ _ p B Bs x L D J hH hq hN'
  by_cases hD : GGCorFiveTwentyWeylDom p B Bs x L D J
  · exact hW G p B Bs x L D J hH hq hN' hD
  · exact hN G p B Bs x L D J hH hq hN' hD


end CFSG.StandardType
