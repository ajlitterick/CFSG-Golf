module

public import CFSG.RankThree.PartTwo.Notation
public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec3

open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type*} [Group G]

@[expose] def thompsonOf (T : Subgroup G) : Subgroup G :=
  (CFSG.higherElemThompson T 0).map T.subtype

@[expose] def omegaZOf (Q : Subgroup G) : Subgroup G :=
  (CFSG.omegaOneCenter (⊤ : Subgroup Q)).map Q.subtype

structure IsChiefSeriesUnder (L V : Subgroup G) (r : ℕ) (Vs : Fin (r + 1) → Subgroup G) :
    Prop where
  zero : Vs 0 = ⊥
  last : Vs (Fin.last r) = V
  normalized : ∀ i, L ≤ Subgroup.normalizer (Vs i : Set G)
  lt : ∀ i : Fin r, Vs i.castSucc < Vs i.succ
  irreducible : ∀ (i : Fin r) (W : Subgroup G), Vs i.castSucc ≤ W → W ≤ Vs i.succ →
    L ≤ Subgroup.normalizer (W : Set G) → W = Vs i.castSucc ∨ W = Vs i.succ


@[expose] def Item321Split : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X L T : Subgroup G) (n : ℕ),
    CFSG.generalizedFitting X = CFSG.pCore 2 X → L ∈ oTwoComponentsIn X →
    X ≤ Subgroup.normalizer (L : Set G) →
    CFSG.ABGLocalTools.IsSylowOf 2 T X → L ⊔ T = X → Odd n →
    Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 n)) →
      (X ≤ Subgroup.normalizer (thompsonOf T : Set G) ∨
          ⁅omegaZOf (CFSG.Open.pCoreOf 2 X), L⁆ = ⊥) ∨
        L ⊔ CFSG.Open.pCoreOf 2 X = X


end CFSG.RankThree.PartTwo.Sec3
