module

public import CFSG.Milestones.ASVolI.A1

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChA

namespace ChA

section A6Vocabulary

variable {G : Type} [Group G]

@[expose] def conjClass (x : G) : Set G :=
  {y | ∃ g : G, y = g⁻¹ * x * g}

structure HasTwoInvolutionClasses (G : Type) [Group G] (z t : G) : Prop where
  z_inv : z ≠ 1 ∧ z ^ 2 = 1
  t_inv : t ≠ 1 ∧ t ^ 2 = 1
  distinct : t ∉ conjClass z
  all : ∀ x : G, x ≠ 1 → x ^ 2 = 1 → x ∈ conjClass z ∨ x ∈ conjClass t

@[expose] def pairSet (z t x : G) : Set (G × G) :=
  {p | p.1 ∈ conjClass z ∧ p.2 ∈ conjClass t ∧ x ∈ Subgroup.zpowers (p.1 * p.2)}

@[expose] noncomputable def aCount (z t x : G) : ℕ :=
  Nat.card (pairSet z t x)

@[expose] def pairSetI (z t x : G) (i : ℕ) : Set (G × G) :=
  {p | p ∈ pairSet z t x ∧ orderOf (p.1 * p.2) % 4 = (if i = 1 then 0 else 2)}

@[expose] noncomputable def aiCount (z t x : G) (i : ℕ) : ℕ :=
  Nat.card (pairSetI z t x i)

@[expose] def bSet (x : G) (i : ℕ) : Set G :=
  {u | u ∈ conjClass x ∧ u ∈ Subgroup.centralizer ({x} : Set G) ∧
    ((u * x ∈ conjClass u) ↔ i = 1)}

@[expose] noncomputable def bCount (x : G) (i : ℕ) : ℕ :=
  Nat.card (bSet x i)

@[expose] def cSet (x : G) (i : ℕ) : Set G :=
  {u | u ≠ 1 ∧ u ^ 2 = 1 ∧ u ∉ conjClass x ∧ u ∈ Subgroup.centralizer ({x} : Set G) ∧
    ((u * x ∈ conjClass u) ↔ i = 1)}

@[expose] noncomputable def cCount (x : G) (i : ℕ) : ℕ :=
  Nat.card (cSet x i)

end A6Vocabulary

end ChA

@[expose] def A_6_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G), HasTwoInvolutionClasses G z t →
    Nat.card G = Nat.card (Subgroup.centralizer ({z} : Set G)) * aCount z t t +
      Nat.card (Subgroup.centralizer ({t} : Set G)) * aCount z t z

section BurnsideA6

section A6Basic

variable {G : Type} [Group G]


end A6Basic

section A6Dihedral

variable {G : Type} [Group G]


end A6Dihedral

section A6Pairs

variable {G : Type} [Group G]


end A6Pairs

section A6Count

variable {G : Type} [Group G]


end A6Count

section A6C

variable {G : Type} [Group G]


end A6C

section A6D

variable {G : Type} [Group G]


end A6D

end BurnsideA6


@[expose] def A_6_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G), HasTwoInvolutionClasses G z t →
    ∀ x : G, x ≠ 1 → x ^ 2 = 1 → ∀ i : ℕ, (i = 1 ∨ i = 2) →
      aiCount z t x i ≤ bCount x i * cCount x i


@[expose] def A_6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G), HasTwoInvolutionClasses G z t →
    ∀ i : ℕ, (i = 1 ∨ i = 2) →
      (cCount t i : ℚ) = (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℚ) * cCount z (3 - i) /
        Nat.card (Subgroup.centralizer ({z} : Set G))


@[expose] def A_6_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G), HasTwoInvolutionClasses G z t →
    (Subgroup.centralizer ({z} : Set G)).index ≤
      cCount t 1 * (bCount t 1 + bCount z 2) + cCount t 2 * (bCount t 2 + bCount z 1)


@[expose] def A_6_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G), HasTwoInvolutionClasses G z t →
    (∀ u v : G, u ∈ conjClass z → v ∈ conjClass z → u * v = v * u → u * v ≠ 1 →
      u * v ∈ conjClass z) →
    (Subgroup.centralizer ({z} : Set G)).index ≤
      Nat.card (conjClass z ∩ (Subgroup.centralizer ({t} : Set G) : Set G) : Set G) *
        (Nat.card (conjClass z ∩ (Subgroup.centralizer ({t} : Set G) : Set G) : Set G) +
          Nat.card (conjClass z ∩ (Subgroup.centralizer ({z} : Set G) : Set G) : Set G))


end CFSG.ASVolI
