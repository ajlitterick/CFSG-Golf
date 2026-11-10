module

public import CFSG.RankThree.PartTwo.Sec12.Item125
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)


@[expose] def Gap125NonCentralBar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L →
    (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) →
    ∀ E : Subgroup G, Late.IsE27 E → E ≤ lcBar c L → c ∈ E →
      Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9 →
      Nat.card (E ⊓ L : Subgroup G) = 9 →
      ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      ∃ P : Subgroup G, IsSylowOf 3 P
          (Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
        ¬ E ⊓ Sec4.thetaQuotCentralizer L ≤ (Subgroup.center P).map P.subtype


end CFSG.RankThree.PartTwo.Sec12
