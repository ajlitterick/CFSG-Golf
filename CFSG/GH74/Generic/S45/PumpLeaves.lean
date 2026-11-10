module

public import CFSG.GH74.Generic.S45.Final

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


@[expose] def IsPumpOutcome (K : Type) [Group K] : Prop :=
  IsL34Quotient K ∨ LieModel (K ⧸ center K) .PSU 3 2 2 ∨
    NativeSporadic.IsSporadic (K ⧸ center K) .M12 ∨ LieModel K .PSL 2 2 4 ∨
    NativeSporadic.IsSporadic K .J2


@[expose] def B_III8_6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ x : G, orderOf x = 2 → ∀ P : Subgroup G, IsSylowOf 2 P (centralizer ({x} : Set G)) →
      ∀ y : G, y ∈ P → (∀ p ∈ P, p * y = y * p) → orderOf y = 2 →
        (∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ y ∈ S ∧ ∀ s ∈ S, s * y = y * s) →
        (∀ g : G, g * y * g⁻¹ ∈ P → (∀ p ∈ P, p * (g * y * g⁻¹) = (g * y * g⁻¹) * p) →
          ∃ c ∈ centralizer ({x} : Set G), c * y * c⁻¹ = g * y * g⁻¹) →
        ∃ hx : x ∈ centralizer ({y} : Set G),
          (⟨x, hx⟩ : ↥(centralizer ({y} : Set G))) ∈ commutator ↥(centralizer ({y} : Set G))

@[expose] def B_III11_2_1 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], InCalK2 K → IsPumpOutcome K →
    Odd (Nat.card (commutator (Outer K)))

@[expose] def B_IA_5_3g : Prop :=
  ∀ (K : Type) [Group K] [Finite K], NativeSporadic.IsSporadic K .J2 →
    IsSimpleGroup K ∧
      ∃ E : Subgroup K, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a * a = 1) ∧ Nat.card ↥E = 16

end CFSG.GH74.Generic.S45
