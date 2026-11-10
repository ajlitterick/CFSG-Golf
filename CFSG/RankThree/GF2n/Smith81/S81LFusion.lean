module

public import CFSG.RankThree.GF2n.Smith81.S81LGen
public import CFSG.RankThree.GF2n.Smith81.S81CS8
public import CFSG.RankThree.GF2n.Smith81.Sec220Conj
public import CFSG.RankThree.GF2n.Smith81.S81CCases
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]


section Lemma4A2

variable [Finite G] {M Q Z : Subgroup G}


end Lemma4A2

section FusionCore

variable [Finite G] {M Q Z B : Subgroup G} {z v : G}


end FusionCore


@[expose] def Smith212E3LRootStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE3L M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ x : G, x ∈ M → x ∉ Q → IsConj z x →
      ∀ X : Subgroup G, IsZConjugate Z X → x ∈ X →
        (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z


end CFSG.RankThree.GF2n.Smith81
