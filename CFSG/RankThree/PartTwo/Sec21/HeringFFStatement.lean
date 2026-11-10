module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.Assembly
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.LocalRank (thetaT aschbacherSolvableCore)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (ChevalleyExceptionalModel)

section Hypotheses

variable {G : Type} [Group G]

@[expose] def FFNotWeaklyClosed (b : G) : Prop :=
  ∃ g : G, conjugate (Subgroup.zpowers b) g ≤ Subgroup.centralizer ({b} : Set G) ∧
    conjugate (Subgroup.zpowers b) g ≠ Subgroup.zpowers b

@[expose] def FFSylowCommutatorOdd (b : G) : Prop :=
  ∀ B : Subgroup G,
    (∃ P : Sylow 3 ↥(Subgroup.centralizer ({b} : Set G)),
      (P : Subgroup ↥(Subgroup.centralizer ({b} : Set G))).map
        (Subgroup.centralizer ({b} : Set G)).subtype = B) →
    ∀ a ∈ B, a ≠ 1 →
      Odd (Nat.card ↥⁅inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({a} : Set G)), B⁆)

@[expose] def FFSylowHyperplaneOdd (b : G) : Prop :=
  ∀ B : Subgroup G,
    (∃ P : Sylow 3 ↥(Subgroup.centralizer ({b} : Set G)),
      (P : Subgroup ↥(Subgroup.centralizer ({b} : Set G))).map
        (Subgroup.centralizer ({b} : Set G)).subtype = B) →
    ∀ B₀ : Subgroup G, B₀ ≤ B → B₀.relIndex B = 3 → Odd (Nat.card ↥(thetaT 3 B₀))

end Hypotheses


end CFSG.RankThree.PartTwo.Sec21
