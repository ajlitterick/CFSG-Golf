module

public import CFSG.Milestones.ASVolI.J2
public import CFSG.Quasithin.Recognition.RuTypeJ36f

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open

@[expose] def IsPOnePlusTwoGroup (p : ℕ) (X : Type) [Group X] : Prop :=
  Nat.card X = p ^ 3 ∧ Monoid.exponent X = p ∧ ∃ a b : X, a * b ≠ b * a

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChIJK

@[expose] def J_3_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    Nat.card G = 2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29

section BurnsideJ5


end BurnsideJ5

section


end

@[expose] def J_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ z : G, Subgroup.zpowers z = ZRu T →
      ∀ u ∈ conjClass z, ∀ v ∈ conjClass z, u * v = v * u → u * v ≠ 1 → u * v ∈ conjClass z

section


end

@[expose] def J_3_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ B7 : Subgroup G, B7 ≤ L → Nat.card ↥B7 = 7 →
    ∀ z s : G, Subgroup.zpowers z = ZRu T → s ∈ S0Ru L B7 → s ≠ 1 →
      (conjClass z ∩ (Subgroup.centralizer ({s} : Set G) : Set G)).ncard =
          (involutionsOf (LsRu s)).ncard ∧
        (involutionsOf (LsRu s)).ncard = 5 * 7 * 13 ∧ 5 * 7 * 13 = 455

section


end

@[expose] def J_3_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ z : G, Subgroup.zpowers z = ZRu T →
      (conjClass z ∩ (HRu T : Set G)).ncard = 1391

section BurnsideJ34


section BurnsideJ28Cnt


end BurnsideJ28Cnt

section BurnsideJ28Hside


end BurnsideJ28Hside

section BurnsideJ28Three4


end BurnsideJ28Three4


end BurnsideJ34

section


end

@[expose] def J_3_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    (HRu T).index ≤ 5 * 7 * 13 * 1846 ∧ 5 * 7 * 13 * 1846 < (3 ^ 2 * 5 ^ 2 * 7 * 13) * 42

section


end

@[expose] def J_3_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ z : G, Subgroup.zpowers z = ZRu T →
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) →
      ∃ R : Subgroup G,
        Subgroup.normalizer (B5 : Set G) =
          (CFSG.generalizedFitting ↥(Subgroup.normalizer (B5 : Set G))).map
            (Subgroup.normalizer (B5 : Set G)).subtype ⊔ R ∧
        IsPOnePlusTwoGroup 5
          ↥((CFSG.generalizedFitting ↥(Subgroup.normalizer (B5 : Set G))).map
            (Subgroup.normalizer (B5 : Set G)).subtype) ∧
        IsSylowIn 5 ((CFSG.generalizedFitting ↥(Subgroup.normalizer (B5 : Set G))).map
            (Subgroup.normalizer (B5 : Set G)).subtype) ⊤ ∧
        Nonempty (↥R ≃* WreathedTwoGroup 2) ∧
        z ∈ R ∧ ∀ r ∈ R, r * z = z * r

section BurnsideJ6b


end BurnsideJ6b

section


end

end CFSG.ASVolI
