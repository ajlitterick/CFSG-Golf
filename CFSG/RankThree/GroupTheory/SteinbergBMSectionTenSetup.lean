module

public import CFSG.RankThree.GroupTheory.SteinbergBYAschVanishing
public import CFSG.RankThree.GroupTheory.SteinbergCEAschbacherPrimeSelector
public import CFSG.Foundations.Catalog

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG CFSG.RankThree.GroupTheory

@[expose] def sectionTenPrimeSet (G : Type*) [Group G] [Finite G] : Set ℕ :=
  {r : ℕ | r.Prime ∧ 3 < r ∧ r ∈ CFSG.Assembly.RankThreeEven.sigmaA G ∧
    SteinbergBY.AschVanishing G r ∧
    ∃ E : Subgroup G, IsElementaryAbelian r E ∧ Nat.card E = r ^ 3 ∧
      ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ normalizer (S : Set G)}

@[expose] def SectionTenSetup (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) :
    Prop :=
  IsSimpleGroup G ∧ (∃ a b : G, a * b ≠ b * a) ∧ IsKProper G ∧ IsCharacteristicPType G 2 ∧
    twoLocalOddRank G = 3 ∧ p ∈ sectionTenPrimeSet G ∧ IsElementaryAbelian p A ∧
    Nat.card A = p ^ 3 ∧
    (∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ normalizer (S : Set G)) ∧
    ((∃ r ∈ sectionTenPrimeSet G, 7 < r) → 7 < p)


end CFSG.RankThree.GroupTheory.SteinbergBM
