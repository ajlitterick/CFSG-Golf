module

public import CFSG.Milestones.ASVolI.I3
public import CFSG.Milestones.ASVolI.I6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.TightEmbedding
public import CFSG.ClassicalInvolution.TwoGroupCase.TwoGroupTI
public import CFSG.ClassicalInvolution.TwoGroupCase.TightPairDihedral
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import Certificates.Kernel.Sporadic.Fi22.C2068

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open
open scoped MatrixGroups

section Tight

variable {G : Type} [Group G]

@[expose] def IsTightlyEmbedded (K : Subgroup G) : Prop :=
  Even (Nat.card ↥K) ∧ ∀ g : G, g ∉ Subgroup.normalizer (K : Set G) →
    Odd (Nat.card ↥(K ⊓ CFSG.conjugate K g))

@[expose] def IsTightlyEmbeddedIn (T S : Subgroup G) : Prop :=
  T ≤ S ∧ Even (Nat.card ↥T) ∧ ∀ s ∈ S, s ∉ Subgroup.normalizer (T : Set G) →
    Odd (Nat.card ↥(T ⊓ CFSG.conjugate T s))

@[expose] def IsTIIn (T S : Subgroup G) : Prop :=
  T ≤ S ∧ ∀ s ∈ S, s ∉ Subgroup.normalizer (T : Set G) → T ⊓ CFSG.conjugate T s = ⊥

@[expose] def IsTIUnder (Q M : Subgroup G) : Prop :=
  ∀ m ∈ M, CFSG.conjugate Q m ≠ Q → Q ⊓ CFSG.conjugate Q m = ⊥

@[expose] def IsSylowTwoIn (Q M : Subgroup G) : Prop :=
  Q ≤ M ∧ IsPGroup 2 Q ∧ ¬ 2 ∣ (Q.subgroupOf M).index

@[expose] def IsSpecialGroup (W : Subgroup G) : Prop :=
  frattiniOf W = centerOf W ∧ ⁅W, W⁆ = centerOf W

structure HypI7 (K H Q S : Subgroup G) : Prop where
  tight : IsTightlyEmbedded K
  Q_ne_bot : Q ≠ ⊥
  Q_sylow : IsSylowTwoIn Q (H ⊓ K)
  S_le : S ≤ H
  S_two : IsPGroup 2 S
  Q_le_S : Q ≤ S

end Tight

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def I_7_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K H Q S : Subgroup G), HypI7 K H Q S →
    Q = S ⊓ K ∧
    (∀ g ∈ H, Q ≠ CFSG.conjugate Q g → CFSG.conjugate Q g ≤ S → Q ⊓ CFSG.conjugate Q g = ⊥) ∧
    (Q ≤ S ∧ IsTIUnder Q (Subgroup.normalizer (S : Set G))) ∧
    (∀ T : Subgroup G, T ≠ ⊥ → IsTIIn T S → IsTightlyEmbeddedIn T S) ∧
    (∀ X : Subgroup G, X ≠ ⊥ → X ≤ Q →
      Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
      S ⊓ Subgroup.normalizer (X : Set G) ≤ S ⊓ Subgroup.normalizer (Q : Set G))

section BurnsideIa


end BurnsideIa


@[expose] def I_7_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K H Q S : Subgroup G), HypI7 K H Q S →
    Q.relIndex S ≤ Nat.card ↥Q → IsNormalIn Q S


@[expose] def I_7_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K H Q S : Subgroup G), HypI7 K H Q S →
    ∀ g ∈ H, Q ≠ CFSG.conjugate Q g →
      CFSG.conjugate Q g ≤ S ⊓ Subgroup.normalizer (Q : Set G) →
      IsDirectProductOf Q (CFSG.conjugate Q g) (Q ⊔ CFSG.conjugate Q g)


@[expose] def I_7_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K H Q S : Subgroup G), HypI7 K H Q S →
    frattiniOf Q ≠ ⊥ →
      ∀ h ∈ H, ∀ k ∈ H, CFSG.conjugate Q h ≤ S → CFSG.conjugate Q k ≤ S →
        CFSG.conjugate Q h ≠ CFSG.conjugate Q k →
        IsDirectProductOf (CFSG.conjugate Q h) (CFSG.conjugate Q k)
          (CFSG.conjugate Q h ⊔ CFSG.conjugate Q k)

section BurnsideIb


abbrev burnsideIb_N {G : Type} [Group G] (S X : Subgroup G) : Subgroup G :=
  S ⊓ Subgroup.normalizer (X : Set G)


structure burnsideIb_EAData {G : Type} [Group G] (S S₀ R : Subgroup G) : Prop where
  two : IsPGroup 2 S
  S₀_le : S₀ ≤ S
  S₀_norm : ∀ s ∈ S, ∀ x ∈ S₀, s * x * s⁻¹ ∈ S₀
  R_le : R ≤ S
  R_inf : S₀ ⊓ R = ⊥
  S_eq : ∀ s ∈ S, ∃ a ∈ S₀, ∃ r ∈ R, s = a * r
  R_comm : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r
  R_exp : ∀ r ∈ R, r * r = 1
  four_le : 4 ≤ Nat.card R
  N_comm : ∀ a ∈ burnsideIb_N S R, ∀ b ∈ burnsideIb_N S R, a * b = b * a
  N_exp : ∀ a ∈ burnsideIb_N S R, a * a = 1
  N_card : Nat.card (burnsideIb_N S R) = Nat.card R * Nat.card R
  S₁_card : Nat.card (S₀ ⊓ burnsideIb_N S R : Subgroup G) = Nat.card R
  cent : ∀ r ∈ R, r ≠ 1 → ∀ g ∈ S, g * r = r * g → g ∈ Subgroup.normalizer (R : Set G)

namespace burnsideIb_EAData

variable {G : Type} [Group G] {S S₀ R : Subgroup G} (h : burnsideIb_EAData S S₀ R)
include h


end burnsideIb_EAData


end BurnsideIb


@[expose] def I_7_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K H Q S : Subgroup G), HypI7 K H Q S →
    ∀ g ∈ H, Q ≠ CFSG.conjugate Q g → CFSG.conjugate Q g ≤ S →
      CFSG.conjugate Q g ⊓ Subgroup.normalizer (Q : Set G) ≠ ⊥ →
      IsDirectProductOf Q (CFSG.conjugate Q g) (Q ⊔ CFSG.conjugate Q g)


@[expose] def I_7_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsTightlyEmbedded K →
    ∀ g : G, g ∉ Subgroup.normalizer (K : Set G) →
    ∀ R : Subgroup G, R ≠ ⊥ →
      IsSylowTwoIn R (K ⊓ Subgroup.normalizer (CFSG.conjugate K g : Set G)) →
      ∀ S : Subgroup G, R ≤ S → IsSylowTwoIn S (CFSG.conjugate K g ⊔ R) →
        (IsDirectProductOf (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G)) R
            (S ⊓ Subgroup.normalizer (R : Set G)) ∧
          S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G) =
            S ⊓ CFSG.conjugate K g ⊓ Subgroup.centralizer (R : Set G)) ∧
        Nonempty (↥(S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G)) ≃* ↥R) ∧
        IsSylowTwoIn (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G))
          (CFSG.conjugate K g ⊓ Subgroup.normalizer (K : Set G)) ∧
        (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G) < S ⊓ CFSG.conjugate K g →
          ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧
        (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G) < S ⊓ CFSG.conjugate K g →
          (Nat.card ↥R = 2 ∧
            ((∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ k))) ∨
              (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥S ≃* SemidihedralGroup n)))) ∨
          (conjClosure R S = R ⊔ (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G)) ∧
            IsDirectProductOf R (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G))
              (conjClosure R S) ∧ Nonempty (↥(conjClosure R S) ≃* (↥R × ↥R))) ∨
          (∃ n : ℕ, 2 ≤ n ∧ IsElemAbelian 2 R ∧ Nat.card ↥R = 2 ^ n ∧
            IsSpecialGroup (conjClosure R S) ∧ Nat.card ↥(conjClosure R S) = 2 ^ (3 * n) ∧
            centerOf (conjClosure R S) =
              S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G) ∧
            (conjClosure R S).relIndex S = 2)) ∧
        IsNormalIn (S ⊓ CFSG.conjugate K g ⊓ Subgroup.normalizer (R : Set G))
          (S ⊓ CFSG.conjugate K g)


end CFSG.ASVolI
