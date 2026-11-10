module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Matrix
open scoped MatrixGroups

section Tim77

variable {H : Type} [Group H]

abbrev tim77L (Q : Subgroup H) (h : H) : Subgroup H := Q ⊔ rightConjugate Q h

abbrev tim77B (Q : Subgroup H) (h : H) : Subgroup H :=
  Q ⊓ normalizer (rightConjugate Q h : Set H)

abbrev tim77D (Q : Subgroup H) (h : H) : Subgroup H :=
  rightConjugate Q h ⊓ normalizer (Q : Set H)

abbrev tim77I (Q : Subgroup H) (h : H) : Subgroup H := Q ⊓ rightConjugate Q h

abbrev tim77M (Q : Subgroup H) (h : H) : Subgroup H := tim77B Q h ⊔ tim77D Q h


structure Tim77Facts (Q : Subgroup H) (h : H) : Prop where
  normal : tim77L Q h ≤ normalizer (tim77M Q h : Set H)
  elem : ∀ x ∈ tim77M Q h, ∀ y ∈ tim77M Q h,
    x * y * x⁻¹ * y⁻¹ ∈ tim77I Q h ∧ x * x ∈ tim77I Q h
  lt_D : tim77I Q h < tim77D Q h
  lt_B : tim77B Q h < Q
  le_center : tim77I Q h ≤ centralizer (tim77L Q h : Set H)
  fix : ∀ x ∈ Q, x ∉ tim77B Q h → ∀ m ∈ tim77M Q h,
    x * m * x⁻¹ * m⁻¹ ∈ tim77I Q h → m ∈ tim77B Q h
  fixD : ∀ d ∈ tim77D Q h, d ∉ tim77I Q h → ∀ x ∈ Q,
    x * d * x⁻¹ * d⁻¹ ∈ tim77I Q h → x ∈ tim77B Q h
  card_eq : Nat.card (tim77B Q h) = Nat.card (tim77D Q h)
  cases : 2 * Nat.card (tim77B Q h) = Nat.card Q ∨
    4 * Nat.card (tim77I Q h) ≤ Nat.card (tim77D Q h)

end Tim77

@[expose] def Tim77Lemma24 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (S Q : Subgroup H), IsSylowOf 2 S ⊤ → Q ≤ S →
    IsElemAbelian 2 Q → (∀ h : H, rightConjugate Q h ≤ S → rightConjugate Q h = Q) →
    (∃ x ∈ Q, ∃ h : H, h⁻¹ * x * h ∈ S ∧ h⁻¹ * x * h ∉ Q) →
    ∃ h : H, Tim77Facts Q h

structure IsAffinePlane (P : Type) (lines : Set (Set P)) : Prop where
  line_unique : ∀ p q : P, p ≠ q → ∃! ℓ, ℓ ∈ lines ∧ p ∈ ℓ ∧ q ∈ ℓ
  parallel : ∀ ℓ ∈ lines, ∀ p : P, p ∉ ℓ → ∃! m, m ∈ lines ∧ p ∈ m ∧ Disjoint ℓ m
  nondegenerate : ∃ p q r : P, ¬ ∃ ℓ ∈ lines, p ∈ ℓ ∧ q ∈ ℓ ∧ r ∈ ℓ

@[expose] def OstromWagnerAG24 : Prop :=
  ∀ (P : Type) [Finite P] (lines : Set (Set P)), IsAffinePlane P lines → Nat.card P = 16 →
    ∀ G : Subgroup (Equiv.Perm P), (∀ g ∈ G, ∀ ℓ ∈ lines, (g : P → P) '' ℓ ∈ lines) →
      (∀ p₁ p₂ q₁ q₂ : P, p₁ ≠ p₂ → q₁ ≠ q₂ → ∃ g ∈ G, g p₁ = q₁ ∧ g p₂ = q₂) →
      ∃ T : Subgroup (Equiv.Perm P), T ≤ G ∧ G ≤ normalizer (T : Set (Equiv.Perm P)) ∧
        IsElemAbelian 2 T ∧ Nat.card T = 16 ∧ ∀ p q : P, ∃ t ∈ T, t p = q


end CFSG.ComponentClassification.AS81
