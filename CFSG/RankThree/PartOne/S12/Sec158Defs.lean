module

public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.RankThree.PartOne.S12.Facts

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

variable {G : Type} [Group G]

@[expose] def zeroLayer (p : ℕ) (E : Subgroup G) (b : G) : Subgroup G :=
  Subgroup.closure {x : G | ∃ Y ∈ thetaCompZeroE p E, Y ∈ thetaComponentsAt p b ∧ x ∈ Y}

@[expose] def thetaCompCentralizer (p : ℕ) (D : Subgroup G) : Set (Subgroup G) :=
  (fun L : Subgroup (Subgroup.centralizer (D : Set G)) =>
      L.map (Subgroup.centralizer (D : Set G)).subtype) ''
    thetaComponents p (Subgroup.centralizer (D : Set G))

@[expose] def KF156' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∀ X ∈ thetaCompZeroE p E, X ≤ lieGenerated p E

@[expose] def KF157 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∀ X ∈ thetaCompZeroE p E,
      (∀ e ∈ E, ∃ x ∈ X, ∃ y ∈ Subgroup.centralizer (X : Set G), e = x * y) ∧
        ¬ p ∣ Nat.card ↥(X ⊓ Subgroup.centralizer (X : Set G))

@[expose] def KF158A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∃ t ∈ reflectionSet p E, ∃ K J : Subgroup G, IsKt p E t K ∧ K ≤ J ∧ autMovedInG E t ≤ K ∧
      p * Nat.card ↥(A ⊓ Subgroup.centralizer (J : Set G)) = Nat.card ↥A ∧
      J ∈ thetaCompCentralizer p (A ⊓ Subgroup.centralizer (J : Set G)) ∧
      ∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
        S = ⁅S, A⁆


end CFSG.RankThree.PartOne
