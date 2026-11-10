module

public import CFSG.Milestones.ASVolI.I7
public import CFSG.Goldschmidt.Steps.Fusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section Strong

variable {G : Type} [Group G]

@[expose] def IsStronglyEmbeddedGLS (M : Subgroup G) : Prop :=
  M ≠ ⊤ ∧ Even (Nat.card ↥M) ∧ ∃ T : Subgroup G, IsSylowTwoIn T M ∧
    ∀ Q : Subgroup G, Q ≤ T → Q ≠ ⊥ → Subgroup.normalizer (Q : Set G) ≤ M

@[expose] def involutionNormalClosure (K : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ g : G, ∃ i ∈ K, i ^ 2 = 1 ∧ i ≠ 1 ∧ x = g⁻¹ * i * g}

end Strong

@[expose] def IsBenderGroup (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, StatedClassicalModel X .PSL 2 2 n) ∨ (∃ f : ℕ, SuzukiModel X 2 f) ∨
    (∃ n : ℕ, StatedClassicalModel X .PSU 3 2 n)

@[expose] def IsSU3Group (q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ 2 ∧
    Nonempty (X ≃* ↥(StatedSU 3 q K))

@[expose] def IsBorelSubgroupTwo {X : Type} [Group X] (B : Subgroup X) : Prop :=
  ∃ S : Sylow 2 X, B = Subgroup.normalizer ((S : Subgroup X) : Set X)

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def I_8_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T : Subgroup G), M ≠ ⊤ → Even (Nat.card ↥M) →
    IsSylowTwoIn T M →
    (IsStronglyEmbeddedGLS M ↔ ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ CFSG.conjugate M g))) ∧
    ((∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ CFSG.conjugate M g))) ↔
      (Subgroup.normalizer (T : Set G) ≤ M ∧
        ∀ i ∈ T, i ^ 2 = 1 → i ≠ 1 → Subgroup.centralizer ({i} : Set G) ≤ M)) ∧
    ((Subgroup.normalizer (T : Set G) ≤ M ∧
        ∀ i ∈ T, i ^ 2 = 1 → i ≠ 1 → Subgroup.centralizer ({i} : Set G) ≤ M) ↔
      ∀ t : G, t ^ 2 = 1 → t ≠ 1 → ∃! x : G ⧸ M, t • x = x)

section BurnsideIc


end BurnsideIc


@[expose] def I_8_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsTightlyEmbedded K → ¬ K.Normal →
    (∀ g : G, CFSG.conjugate K g ≠ K →
      Odd (Nat.card ↥(CFSG.conjugate K g ⊓ Subgroup.normalizer (K : Set G)))) →
    (CFSG.pRank 2 ↥(involutionNormalClosure K) = 1 ∧
      ∃ z ∈ K, z ^ 2 = 1 ∧ z ≠ 1 ∧
        involutionNormalClosure K =
          (CFSG.oddCore ↥(involutionNormalClosure K)).map (involutionNormalClosure K).subtype ⊔
            Subgroup.zpowers z) ∨
    (IsBenderGroup (↥(involutionNormalClosure K) ⧸ CFSG.oddCore ↥(involutionNormalClosure K)) ∧
      (CFSG.oddCore ↥(involutionNormalClosure K)).map (involutionNormalClosure K).subtype ≤
        Subgroup.normalizer (K : Set G) ∧
      IsBorelSubgroupTwo
        (((Subgroup.normalizer (K : Set G)).subgroupOf (involutionNormalClosure K)).map
          (QuotientGroup.mk' (CFSG.oddCore ↥(involutionNormalClosure K)))))


@[expose] def I_8_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSylowTwoIn T ⊤ →
    ∀ V : Subgroup G, IsElemAbelian 2 V → IsTISubgroup V →
      CFSG.IsStronglyClosedIn T (V : Set G) → 0 < CFSG.pRank 2 ↥V → ¬ V.Normal →
        (CFSG.pRank 2 ↥V = 1 ∧
          conjClosure V ⊤ =
            (CFSG.oddCore ↥(conjClosure V ⊤)).map (conjClosure V ⊤).subtype ⊔ V) ∨
        (1 < CFSG.pRank 2 ↥V ∧ CFSG.IsQuasisimple ↥(conjClosure V ⊤) ∧
          (StatedClassicalModel ↥(conjClosure V ⊤) .PSL 2 2 (CFSG.pRank 2 ↥V) ∨
            SuzukiModel ↥(conjClosure V ⊤) 2 (CFSG.pRank 2 ↥V) ∨
            StatedClassicalModel ↥(conjClosure V ⊤) .PSU 3 2 (CFSG.pRank 2 ↥V) ∨
            IsSU3Group (2 ^ CFSG.pRank 2 ↥V) ↥(conjClosure V ⊤)) ∧
          V = omegaOne (T ⊓ conjClosure V ⊤))


@[expose] def I_8_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSylowTwoIn T ⊤ →
    ∀ V : Subgroup G, (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) → CFSG.IsStronglyClosedIn T (V : Set G) →
      ControlsFusionOfElements (Subgroup.normalizer (V : Set G)) V ∧
      (IsTISubgroup V ↔
        ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (V : Set G))


@[expose] def I_8_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V : Subgroup G), M ≠ ⊤ → V ≠ ⊥ → V ≤ M →
    IsNormalIn V M → IsElemAbelian 2 V →
    (∀ v ∈ V, v ≠ 1 → ∃! x : G ⧸ M, v • x = x) →
      ((Nat.card ↥V = 2 ∧
          conjClosure V ⊤ =
            (CFSG.oddCore ↥(conjClosure V ⊤)).map (conjClosure V ⊤).subtype ⊔ V) ∨
        (CFSG.IsQuasisimple ↥(conjClosure V ⊤) ∧
          IsBenderGroup (↥(conjClosure V ⊤) ⧸ Subgroup.center ↥(conjClosure V ⊤)) ∧
          (∃ TL : Subgroup G, IsSylowTwoIn TL (conjClosure V ⊤) ∧ V = omegaOne TL) ∧
          M ⊓ conjClosure V ⊤ = conjClosure V ⊤ ⊓ Subgroup.normalizer (V : Set G) ∧
          ∃ S : Subgroup G, IsSylowTwoIn S (conjClosure V ⊤) ∧
            M ⊓ conjClosure V ⊤ = conjClosure V ⊤ ⊓ Subgroup.normalizer (S : Set G))) ∧
      (∃ (_ : ((Subgroup.centralizer (V : Set G)).subgroupOf M).Normal),
        Group.IsSolvable (↥M ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf M))


end CFSG.ASVolI
