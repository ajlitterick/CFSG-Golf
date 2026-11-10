module

public import CFSG.RankThree.CentralCover.SteinbergBNOddExtensionRank
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.CentralCover

abbrev centerQuotientMap (X : Type*) [Group X] : X →* X ⧸ Subgroup.center X :=
  QuotientGroup.mk' (Subgroup.center X)

abbrev centerPCore (p : ℕ) (X : Type) [Group X] : Subgroup X :=
  inSubgroup (CFSG.pCore p) (Subgroup.center X)

@[expose] def CentralOddExtensionExactlyOneCase {P : Type*} [Group P] (A : Subgroup P) [A.Normal]
    (p d : ℕ) : Prop :=
  (CentralOddExtensionCaseOne A p d ∨ CentralOddExtensionCaseTwo A p d ∨
      CentralOddExtensionCaseThree A p d) ∧
    ¬ (CentralOddExtensionCaseOne A p d ∧ CentralOddExtensionCaseTwo A p d) ∧
    ¬ (CentralOddExtensionCaseOne A p d ∧ CentralOddExtensionCaseThree A p d) ∧
    ¬ (CentralOddExtensionCaseTwo A p d ∧ CentralOddExtensionCaseThree A p d)


end CFSG.RankThree.PartOne
