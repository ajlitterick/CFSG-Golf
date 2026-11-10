module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs
public import CFSG.SignalizerFunctorTheorem.Inheritance.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

abbrev Elem2 (n : ℕ) : Type := Multiplicative (Fin n → ZMod 2)

@[expose] def IsExtensionShape (X : Type*) [Group X] (A B : Type*) [Group A] [Group B] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), Nonempty (N ≃* A) ∧ Nonempty (X ⧸ N ≃* B)

@[expose] def IsShapeTwoTwoSixS5 (X : Type*) [Group X] : Prop :=
  ∃ (V N : Subgroup X) (_ : V.Normal) (_ : N.Normal), V ≤ N ∧ Nonempty (V ≃* Elem2 2) ∧
    Nonempty (N ⧸ V.subgroupOf N ≃* Elem2 6) ∧ Nonempty (X ⧸ N ≃* Equiv.Perm (Fin 5))

@[expose] def IsShapeTwoTwoTimesA8 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Elem2 2 × alternatingGroup (Fin 8))

@[expose] def IsShapeTwoTwoTimesTwoFourA5 (X : Type*) [Group X] : Prop :=
  ∃ (Y : Type) (_ : Group Y), IsExtensionShape Y (Elem2 4) (alternatingGroup (Fin 5)) ∧
    Nonempty (X ≃* Elem2 2 × Y)

@[expose] def IsNonsplitDoubleCoverOfS5 (Y : Type*) [Group Y] : Prop :=
  ∃ (Z : Subgroup Y) (_ : Z.Normal), Nat.card Z = 2 ∧ Nonempty (Y ⧸ Z ≃* Equiv.Perm (Fin 5)) ∧
    Z ≤ commutator Y


@[expose] def IsShapeCentralizerThree (X : Type*) [Group X] : Prop :=
  ∃ (Y : Type) (_ : Group Y),
    IsExtensionShape Y (Elem2 2 × alternatingGroup (Fin 5)) (Multiplicative (ZMod 2)) ∧
      Nonempty (X ≃* Multiplicative (ZMod 3) × Y)

@[expose] def IsShapeCentralizerFiveA (X : Type*) [Group X] : Prop :=
  ∃ (N S : Subgroup X) (_ : N.Normal), CFSG.IsExtraspecial 5 ↥N ∧ Nat.card N = 5 ^ 3 ∧
    (∀ x : N, x ^ 5 = 1) ∧ Nonempty (S ≃* Multiplicative (ZMod 2) × QuaternionGroup 2) ∧
      N.IsComplement' S

@[expose] def IsShapeCentralizerFiveB (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Multiplicative (ZMod 5) × Multiplicative (ZMod 2) × DihedralGroup 5)

@[expose] def IsShapeCentralizerFiveC (X : Type*) [Group X] : Prop :=
  ∃ (Y : Type) (_ : Group Y), IsNonsplitDoubleCoverOfS5 Y ∧
    Nonempty (X ≃* Multiplicative (ZMod 5) × Y)

@[expose] def IsShapeCentralizerSeven (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Multiplicative (ZMod 7) × Elem2 2)

@[expose] def IsShapeCentralizerEleven (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Multiplicative (ZMod 11) × Multiplicative (ZMod 2))

@[expose] def IsShapeK (K : Type*) [Group K] : Prop :=
  ∃ (N : Subgroup K) (_ : N.Normal), IsPGroup 2 N ∧ Nat.card N = 2 ^ 7 ∧
    Nonempty (K ⧸ N ≃* Equiv.Perm (Fin 5)) ∧
    Nonempty (center N ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) ∧
    ∃ Q : Subgroup N, IsPlusExtraspecial 2 Q ∧ center N ⊔ Q = ⊤ ∧
      Nat.card (center N ⊓ Q : Subgroup N) = 2

structure TwoHSFacts (H : Type) [Group H] (a z b z₁ : H) : Prop where
  center_eq : center H = zpowers a
  orderOf_a : orderOf a = 2
  orderOf_z : orderOf z = 2
  orderOf_b : orderOf b = 2
  orderOf_z₁ : orderOf z₁ = 2
  not_isConj : ∀ i j : Fin 5, i ≠ j →
    ¬ IsConj (![a, z, a * z, b, z₁] i) (![a, z, a * z, b, z₁] j)
  involution_cover : ∀ x : H, orderOf x = 2 → ∃ i : Fin 5, IsConj (![a, z, a * z, b, z₁] i) x
  cent_z : IsShapeTwoTwoSixS5 (centralizer ({z} : Set H))
  cent_az : IsShapeTwoTwoSixS5 (centralizer ({a * z} : Set H))
  cent_b : IsShapeTwoTwoTimesA8 (centralizer ({b} : Set H))
  cent_z₁ : IsShapeTwoTwoTimesTwoFourA5 (centralizer ({z₁} : Set H))
  mem_commutator : a ∈ commutator H ∧ z ∈ commutator H ∧ a * z ∈ commutator H
  not_mem_commutator : b ∉ commutator H ∧ z₁ ∉ commutator H
  K_shape : IsShapeK ↥(commutator H ⊓ centralizer ({z} : Set H))
  center_K : ∀ g : ↥(commutator H ⊓ centralizer ({z} : Set H)),
    g ∈ center ↥(commutator H ⊓ centralizer ({z} : Set H)) ↔ (g : H) ∈ zpowers a ⊔ zpowers z
  exists_sq_eq : ∃ g : H, g ^ 2 = a
  isConj_of_sq_eq : ∀ g g' : H, g ^ 2 = a → g' ^ 2 = a → IsConj g g'
  not_isSectionOf_A8 : ∀ g : H, g ^ 2 = a →
    ¬ CFSG.SignalizerFunctorTheorem.IsSectionOf (alternatingGroup (Fin 8))
      (centralizer ({g} : Set H))
  card_eq : Nat.card H = 2 ^ 11 * 3 ^ 2 * 5 ^ 3 * 7 * 11
  table_three : ∀ x : H, orderOf x = 3 → IsShapeCentralizerThree (centralizer ({x} : Set H))
  table_five : ∀ x : H, orderOf x = 5 →
    IsShapeCentralizerFiveA (centralizer ({x} : Set H)) ∨
      IsShapeCentralizerFiveB (centralizer ({x} : Set H)) ∨
        IsShapeCentralizerFiveC (centralizer ({x} : Set H))
  table_seven : ∀ x : H, orderOf x = 7 → IsShapeCentralizerSeven (centralizer ({x} : Set H))
  table_eleven : ∀ x : H, orderOf x = 11 → IsShapeCentralizerEleven (centralizer ({x} : Set H))
  sl25_le_centralizer : ∀ ρ : H, orderOf ρ = 5 →
    IsShapeCentralizerFiveC (centralizer ({ρ} : Set H)) →
      ∃ S : Subgroup ↥(centralizer ({ρ} : Set H)),
        Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
  sylow_two_five : ∀ ρ : H, orderOf ρ = 5 → IsShapeCentralizerFiveB (centralizer ({ρ} : Set H)) →
    ∀ T : Sylow 2 ↥(centralizer ({ρ} : Set H)), ∃ u : H, IsConj z₁ u ∧
      (T : Subgroup ↥(centralizer ({ρ} : Set H))).map (centralizer ({ρ} : Set H)).subtype =
        closure {a, u}
  m11_unique_class : (∃ M : Subgroup H, IsSporadic ↥M .M11) ∧
    ∀ M M' : Subgroup H, IsSporadic ↥M .M11 → IsSporadic ↥M' .M11 →
      ∃ g : H, M' = M.map (MulAut.conj g).toMonoidHom
  m11_centralizer_five : ∀ M : Subgroup H, IsSporadic ↥M .M11 → ∀ ρ ∈ M, orderOf ρ = 5 →
    IsShapeCentralizerFiveB (centralizer ({ρ} : Set H))
  centralizer_five_of_A8 : ∀ c : H, orderOf c = 2 →
    IsShapeTwoTwoTimesA8 (centralizer ({c} : Set H)) →
      ∀ ρ : H, orderOf ρ = 5 → ρ * c = c * ρ → IsShapeCentralizerFiveC (centralizer ({ρ} : Set H))

structure TwoHSInterface : Prop where
  nonempty_mulEquiv : ∀ (H H' : Type) [Group H] [Group H'] (E : Subgroup H) (E' : Subgroup H'),
    TwoHS.IsF5Centralizer H E → TwoHS.IsF5Centralizer H' E' → Nonempty (H ≃* H')
  facts : ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∃ a z b z₁ : H, TwoHSFacts H a z b z₁

@[expose] def centerOf {C : Type*} [Group C] (Q : Subgroup C) : Subgroup C :=
  Q ⊓ centralizer (Q : Set C)

structure AschbacherHyp (C : Type) [Group C] (Q : Subgroup C) [Q.Normal] : Prop
    extends IsExtraspecialPlusByA5WrTwoWith C Q where
  irreducible : ∀ W : Subgroup C, centerOf Q ≤ W → W ≤ Q →
    (∀ g ∈ commutator C, ∀ w ∈ W, g * w * g⁻¹ ∈ W) → W = centerOf Q ∨ W = Q
  no_involution : ∀ t ∈ commutator C, t ^ 2 = 1 →
    ¬ Nonempty (↥(centralizer ({(t : C ⧸ Q)} : Set (C ⧸ Q)) ⊓
      (commutator C).map (QuotientGroup.mk' Q)) ≃* Elem2 2 × alternatingGroup (Fin 5))
  exists_involution : ∃ t : C, t ∉ commutator C ∧ t ^ 2 = 1 ∧ ∀ T : Sylow 2 C, t ∈ T →
    ∃ x ∈ Q, (∀ s ∈ (T : Subgroup C) ⊓ commutator C, ⁅x, s⁆ ∈ centerOf Q) ∧
      ⁅t, x⁆ ∉ centerOf Q

@[expose] def AschbacherDichotomy : Prop :=
  ∀ (L : Type) [Group L] (Q : Subgroup L) [Q.Normal], IsPlusExtraspecial 4 Q →
    centralizer (Q : Set L) ≤ Q →
    Nonempty (L ⧸ Q ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) →
      ((∀ W : Subgroup L, centerOf Q ≤ W → W ≤ Q → (∀ g : L, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
          W = centerOf Q ∨ W = Q) ↔
        ∃ q ∈ Q, q ∉ centerOf Q ∧ ∃ S : Subgroup (L ⧸ Q),
          (∀ x : L ⧸ Q, x ∈ S ↔ ∃ g : L, (g : L ⧸ Q) = x ∧ ⁅g, q⁆ ∈ centerOf Q) ∧
            Nonempty (S ≃* alternatingGroup (Fin 5)))

@[expose] def HaradaHalf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ t : G, orderOf t = 2 →
      ∀ E : Subgroup (centralizer ({t} : Set G)),
        TwoHS.IsF5Centralizer (centralizer ({t} : Set G)) E →
          ∃ z : G, orderOf z = 2 ∧ IsExtraspecialPlusByA5WrTwo (centralizer ({z} : Set G))

structure HNSideFacts : Prop where
  finite : Finite (Carrier .HN)
  isSimpleGroup : IsSimpleGroup (Carrier .HN)
  isF5Type : ∃ a z : Carrier .HN, IsF5Type a z
  isF5Centralizer_of_component : ∀ z₀ : Carrier .HN, orderOf z₀ = 2 →
    (∃ K : Subgroup (centralizer ({z₀} : Set (Carrier .HN))), CFSG.IsComponent K) →
      ∃ E : Subgroup (centralizer ({z₀} : Set (Carrier .HN))),
        TwoHS.IsF5Centralizer (centralizer ({z₀} : Set (Carrier .HN))) E

end CFSG.EvenSporadicStandard.HNRecog
