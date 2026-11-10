module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.GroupTheory.SteinbergBMSectionTenSetup
public import CFSG.RankThree.GroupTheory.SteinbergCESectionTenStrata

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Blueprint (LieModel EvenLieType)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def InducesFieldAut (p : ℕ) (a : G) (J : Subgroup G) : Prop :=
  a ∈ Subgroup.normalizer (J : Set G) ∧ a ∉ J ⊔ Subgroup.centralizer (J : Set G) ∧
    a ^ p ∈ J ⊔ Subgroup.centralizer (J : Set G) ∧
    ∃ (t : StatedLieTag) (n f : ℕ), 1 ≤ f ∧ LieModel (J ⧸ Subgroup.center J) t n 2 (p * f) ∧
      (LieModel (↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({a} : Set G))) ⧸
        Subgroup.center ↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({a} : Set G))))
        t n 2 f ∨
      (t = .twistedF4 ∧ n = 0 ∧ f = 1 ∧
        LieModel (↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({a} : Set G))) ⧸
          Subgroup.center ↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({a} : Set G))))
          .Tits 0 2 1))

@[expose] def InSec11Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ c ∈ A, c ≠ 1 → ∀ J ∈ sectionTenAt p (sectionTenZeroStar p A ∩ sectionTenTwo p A) c,
      EvenLieType (J ⧸ Subgroup.center J) ∧ ¬ p ∣ Nat.card (Subgroup.center J) ∧
      ∃ a d : G, a ∈ A ∧ d ∈ A ∧ d ≠ 1 ∧
        A = Subgroup.zpowers a ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers d ∧
        Subgroup.zpowers d = A ⊓ J ∧ InducesFieldAut p a J


end CFSG.RankThree.PartOne
