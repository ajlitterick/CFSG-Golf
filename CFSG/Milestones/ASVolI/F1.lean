module

public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.Background.RonanF13Core
import CFSG.Quasithin.Background.RonanF13Listed

public section

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

abbrev HypF_1_1 {G : Type} [Group G] (L₁ L₂ S : Subgroup G) : Prop := Hyp111 L₁ L₂ S

@[expose] def IsHallTwoPrime {G : Type} [Group G] (D X : Subgroup G) : Prop :=
  D ≤ X ∧ Odd (Nat.card D) ∧ ∃ k : ℕ, D.relIndex X = 2 ^ k

@[expose] def F13Conclusion {G : Type} [Group G] (Li Lj S : Subgroup G) : Prop :=
  ((borelOf Li S ≠ Li ∧ S ⊓ Li ≤ borelOf Li S ∧
      (∀ M : Subgroup G, S ⊓ Li ≤ M → M ≤ Li → M ≠ Li → M ≤ borelOf Li S)) ∧
    ((borelOf Li S).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li)) =
      Subgroup.normalizer
        ((((S ⊓ Li).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li)) :
          Subgroup (↥Li ⧸ pCore 2 ↥Li)) : Set (↥Li ⧸ pCore 2 ↥Li)) ∧
    (IsPGroup 2 (((S ⊓ Li).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li))) ∧
      ¬ 2 ∣ (((S ⊓ Li).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li))).index) ∧
    pCoreOf 2 (borelOf Li S) = S ⊓ Li) ∧
  borelOf Lj S = Lj ⊓ Subgroup.normalizer (Li : Set G) ∧
  (borelOf Lj S ≤ Subgroup.normalizer (borelOf Li S : Set G) ∧
    borelOf Lj S ≤ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G)) ∧
  (borelOf Li S ⊔ borelOf Lj S ⊔ S =
      (Li ⊔ S ⊔ borelOf Lj S) ⊓ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) ∧
    Group.IsSolvable ↥(borelOf Li S ⊔ borelOf Lj S ⊔ S)) ∧
  (∃ Di Dj : Subgroup G, IsHallTwoPrime Di (borelOf Li S) ∧ IsHallTwoPrime Dj (borelOf Lj S) ∧
      borelOf Li S = (S ⊓ Li) ⊔ Di ∧ borelOf Lj S = (S ⊓ Lj) ⊔ Dj ∧
      Di ≤ Subgroup.normalizer (Dj : Set G) ∧
      borelOf Li S ⊔ borelOf Lj S ⊔ S = S ⊔ Di ⊔ Dj ∧
      (∀ x ∈ Di ⊔ Dj, ∀ y ∈ Di ⊔ Dj, x * y = y * x) ∧
      IsHallTwoPrime (Di ⊔ Dj) (borelOf Li S ⊔ borelOf Lj S ⊔ S)) ∧
  ((Li ⊔ (borelOf Li S ⊔ borelOf Lj S ⊔ S)) ⊓ (Lj ⊔ (borelOf Li S ⊔ borelOf Lj S ⊔ S)) =
    borelOf Li S ⊔ borelOf Lj S ⊔ S)

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.ASVolI.ChF

@[expose] def F_1_2 : Prop :=
  ∀ (G : Type) [Group G] (L₁ L₂ S : Subgroup G),
    (HypF_1_1 L₁ L₂ S →
      ∀ (Li Lj : Subgroup G), (Li = L₁ ∧ Lj = L₂) ∨ (Li = L₂ ∧ Lj = L₁) →
        (∃ Dj : Subgroup G, IsHallTwoPrime Dj (borelOf Lj S) ∧ borelOf Lj S = (S ⊓ Lj) ⊔ Dj) ∧
        ∀ Dj : Subgroup G, IsHallTwoPrime Dj (borelOf Lj S) →
          borelOf Lj S = (S ⊓ Lj) ⊔ Dj ∧ Li ⊔ S ⊔ borelOf Lj S = Li ⊔ S ⊔ Dj) ∧
    (∀ (Li Lj : Subgroup G), (Li = L₁ ∧ Lj = L₂) ∨ (Li = L₂ ∧ Lj = L₁) →
      (Finite ↥S ∧ IsPGroup 2 S ∧ S ≤ Subgroup.normalizer (Li : Set G) ∧
          S ≤ Subgroup.normalizer (Lj : Set G)) →
      (IsSylowTwoOf (S ⊓ Li) Li ∧ IsSylowTwoOf (S ⊓ Lj) Lj) →
      (IsRankOneListed (oTwoQuot ↥Li) ∧ IsRankOneListed (oTwoQuot ↥Lj)) →
        ∀ Dj : Subgroup G, IsHallTwoPrime Dj (borelOf Lj S) → Dj ≤ Subgroup.normalizer (Li : Set G) →
          borelOf Lj S ≤ Subgroup.normalizer (Li : Set G))


section Loc

open CFSG.LieType.BorelTits CFSG.Quasithin.F7

variable {G : Type} [Group G]


end Loc

@[expose] def F_1_3 : Prop :=
  ∀ (G : Type) [Group G] (L₁ L₂ S : Subgroup G), HypF_1_1 L₁ L₂ S →
    F13Conclusion L₁ L₂ S ∧ F13Conclusion L₂ L₁ S

section LocF13

open CFSG.Quasithin.RonanF13 (F13Setup)

variable {G : Type} [Group G]


end LocF13

section CertF13


open CFSG.Quasithin.RonanF13 (core5 rankOneTwist_of_listed)


end CertF13

section CertF13Main


end CertF13Main

@[expose] def F_1_5_hypothesis : Prop :=
  ∀ (G : Type) [Group G] (L₁ L₂ S : Subgroup G), HypF_1_1 L₁ L₂ S →
    (L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊓ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) =
      borelOf L₁ S ⊔ borelOf L₂ S ⊔ S ∧
    (RankTwoAmalgam.ofSubgroups (L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))
        (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))).IsInjective

@[expose] def F_1_5 : Prop :=
  (∀ (G : Type) [Group G] (P₁ P₂ : Subgroup G),
    (RankTwoAmalgam.ofSubgroups P₁ P₂).IsInjective) ∧ F_1_5_hypothesis

section CertF15


end CertF15

@[expose] def F_1_6 : Prop :=
  (∀ (G : Type) [Group G] (P₁ P₂ : Subgroup G),
    ∃ c : (RankTwoAmalgam.ofSubgroups P₁ P₂).Completion ↥(P₁ ⊔ P₂), c.IsFaithful ∧
      (∀ g : ↥P₁, ((c.φ1 g : ↥(P₁ ⊔ P₂)) : G) = (g : G)) ∧
      (∀ g : ↥(P₁ ⊓ P₂), ((c.φ12 g : ↥(P₁ ⊔ P₂)) : G) = (g : G)) ∧
      (∀ g : ↥P₂, ((c.φ2 g : ↥(P₁ ⊔ P₂)) : G) = (g : G))) ∧
  (∀ (G : Type) [Group G] (L₁ L₂ S : Subgroup G), HypF_1_1 L₁ L₂ S →
    (L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊔ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) = L₁ ⊔ L₂ ⊔ S ∧
    ∃ c : (RankTwoAmalgam.ofSubgroups (L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))
          (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))).Completion
        ↥((L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊔ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))),
      c.IsFaithful ∧
      (∀ g : ↥(L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)),
        ((c.φ1 g : ↥((L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊔ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)))) : G) =
          (g : G)) ∧
      (∀ g : ↥((L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊓ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))),
        ((c.φ12 g : ↥((L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊔ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)))) : G) =
          (g : G)) ∧
      (∀ g : ↥(L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)),
        ((c.φ2 g : ↥((L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊔ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)))) : G) =
          (g : G))) ∧
  (∀ (α : RankTwoAmalgam.{0}) (Y : Type) [Group Y] (c : α.Completion Y),
    Function.Surjective (Amalgam.Completion.hat c.toCompletion) ∧
    ∀ (d : RankTwoIndex) (x : α.X d),
      Amalgam.Completion.hat c.toCompletion (Amalgam.ξ α.toAmalgam d x) = c.homFamily d x)


@[expose] def F_1_10 : Prop :=
  ∀ (G : Type) [Group G] (L₁ L₂ S : Subgroup G), HypF_1_1 L₁ L₂ S →
    ((S = pCoreOf 2 (L₁ ⊔ S) ⊔ (S ⊓ L₁) → S = pCoreOf 2 (L₂ ⊔ S) ⊔ (S ⊓ L₂) →
        borelOf L₁ S ≤ Subgroup.normalizer (S : Set G) ∧ borelOf L₂ S ≤ Subgroup.normalizer (S : Set G)) ∧
    (((borelOf L₁ S ≤ Subgroup.normalizer (S : Set G) ∧ borelOf L₂ S ≤ Subgroup.normalizer (S : Set G)) ∨
        S ≤ L₁ ∨ S ≤ L₂) →
      S = pCoreOf 2 (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S) ∧
      borelOf L₁ S ⊔ borelOf L₂ S ⊔ S =
        borelOf L₁ S ⊔ borelOf L₂ S ⊔ pCoreOf 2 (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)))

section CertF10


end CertF10

@[expose] def F_1_11 : Prop :=
  (∀ α β : RankTwoAmalgam.{0}, Nonempty (α.Iso β) → α.ParabolicIso β) ∧
  (∃ α β : RankTwoAmalgam.{0}, α.IsInjective ∧ β.IsInjective ∧ α.ParabolicIso β ∧ ¬ Nonempty (α.Iso β))


end CFSG.ASVolI
