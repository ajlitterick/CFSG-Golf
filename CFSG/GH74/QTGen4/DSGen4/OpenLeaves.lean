module

public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.GH74.QTGen4.Finite4

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

@[expose] def LeafSylowS : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G},
    (Hyp111R L1 L2 S) →
    IsSylowTwoOf S (bigB L1 L2 S) ∧ IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) ∧
      pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S


@[expose] def LeafFaithfulA5 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P L E K : Subgroup G},
    (L ≤ P) →
    (P ≤ Subgroup.normalizer (L : Set G)) →
    (E ≤ P) →
    (P ≤ Subgroup.normalizer (E : Set G)) →
    (P ≤ Subgroup.normalizer (K : Set G)) →
    (IsElemSec K E) →
    (K.relIndex E ≤ 16) →
    (IsL2Quot 2 (oTwoQuot ↥L)) →
    (∀ q ∈ pCoreOf 2 P, ∀ e ∈ E, ⁅q, e⁆ ∈ K) →
    (∃ l ∈ L, ∃ e ∈ E, ⁅l, e⁆ ∉ K) →
    A5Chief P L E K


@[expose] def LeafM2 : Prop :=
  ∀ {G : Type} [Group G] [Finite4 G] {L P S : Subgroup G},
    (A5Par L P) →
    (IsSylowTwoOf S P) →
    (pCoreOf 2 P ≤ S) →
    (pCoreOf 2 P).relIndex S ∣ 8 ∧ Odd ((pCoreOf 2 P).relIndex (dsCentMod P L (pCoreOf 2 P))) ∧
      (∀ d ∈ P ⊓ Subgroup.normalizer (S : Set G), orderOf d = 3 → (pCoreOf 2 P).relIndex S = 4)

@[expose] def LeafM3 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P L E K T : Subgroup G},
    (A5Chief P L E K) →
    (IsSylowTwoOf T L) →
    (NatSec L K E →
        (∀ X : Subgroup G, K ≤ X → X ≤ E →
          L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G) →
            X = K ∨ X = ⁅E, T⁆ ⊔ K ∨ X = E) ∧
        K.relIndex (⁅E, T⁆ ⊔ K) = 4 ∧
        (∀ t ∈ T, ∀ f ∈ ⁅E, T⁆ ⊔ K, ⁅f, t⁆ ∈ K) ∧
        (∀ e ∈ E, (∀ t ∈ T, ⁅e, t⁆ ∈ K) → e ∈ ⁅E, T⁆ ⊔ K) ∧
        (∀ s ∈ T ⊔ pCoreOf 2 P, s ∉ pCoreOf 2 P → ∀ e ∈ E, e ∉ ⁅E, T⁆ ⊔ K → ⁅e, s⁆ ∉ K)) ∧
      (¬ NatSec L K E →
        (∀ X : Subgroup G, K ≤ X → X ≤ E →
          L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G) →
            X = K ∨ X = ⁅⁅E, T⁆, T⁆ ⊔ K ∨ X = ⁅E, T⁆ ⊔ K ∨ X = E) ∧
        K.relIndex (⁅⁅E, T⁆, T⁆ ⊔ K) = 2 ∧ K.relIndex (⁅E, T⁆ ⊔ K) = 8 ∧
        (∀ t ∈ T, ∀ f ∈ ⁅⁅E, T⁆, T⁆ ⊔ K, ⁅f, t⁆ ∈ K) ∧
        (∀ e ∈ E, (∀ t ∈ T, ⁅e, t⁆ ∈ K) → e ∈ ⁅⁅E, T⁆, T⁆ ⊔ K) ∧
        (∀ d ∈ L ⊓ Subgroup.normalizer (T : Set G), orderOf d = 3 →
          FixFree (⁅⁅E, T⁆, T⁆ ⊔ K) (⁅E, T⁆ ⊔ K) d))

@[expose] def LeafM4 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P L E K T X Y : Subgroup G},
    (A5Chief P L E K) →
    (IsSylowTwoOf T L) →
    (X ≤ T ⊔ pCoreOf 2 P) →
    (⁅⁅E, X⁆, X⁆ ≤ K) →
    (¬ ⁅E, X⁆ ≤ K) →
    (∀ x ∈ X, (∀ e ∈ E, ⁅x, e⁆ ∈ K) → x ∈ pCoreOf 2 P) →
    (K ≤ Y) →
    (Y ≤ E) →
    (∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈ K) →
    (Y.relIndex E ≤ (X ⊓ pCoreOf 2 P).relIndex X) →
    NatSec L K E ∧ X ⊔ pCoreOf 2 P = T ⊔ pCoreOf 2 P ∧ Y.relIndex E = 4

@[expose] def LeafM5 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L T : Subgroup G},
    (IsL2Quot 2 (oTwoQuot ↥L)) →
    (IsSylowTwoOf T L) →
    (∀ X : Subgroup G, pCoreOf 2 L ≤ X → X ≤ T →
        L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G) →
          X = pCoreOf 2 L ∨ X = T) ∧
      (∀ d ∈ L ⊓ Subgroup.normalizer (T : Set G), orderOf d = 3 → FixFree (pCoreOf 2 L) T d)


@[expose] def LeafShort2OfA5 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G},
    (IsL2Quot 2 (oTwoQuot ↥L)) →
    (CharTwo L) →
    (IsElemAbelian 2 (pCoreOf 2 L)) →
    (Nat.card (pCoreOf 2 L) = 16) →
    IsShort2 L

@[expose] def LeafLin2OfNatural : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G},
    (IsL2Quot 2 (oTwoQuot ↥L)) →
    (CharTwo L) →
    (IsElemAbelian 2 (pCoreOf 2 L)) →
    (Nat.card (pCoreOf 2 L) = 16) →
    (NatSec L ⊥ (pCoreOf 2 L)) →
    IsLin2Type L 2

@[expose] def LeafAlt5OfOrth : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G},
    (IsL2Quot 2 (oTwoQuot ↥L)) →
    (CharTwo L) →
    (IsElemAbelian 2 (pCoreOf 2 L)) →
    (Nat.card (pCoreOf 2 L) = 16) →
    (¬ NatSec L ⊥ (pCoreOf 2 L)) →
    IsAltType L 5

@[expose] def LeafOmega4MinusOfOrth : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L : Subgroup G},
    (IsL2Quot 2 (oTwoQuot ↥L)) →
    (CharTwo L) →
    (IsElemAbelian 2 (pCoreOf 2 L)) →
    (Nat.card (pCoreOf 2 L) = 16) →
    (¬ NatSec L ⊥ (pCoreOf 2 L)) →
    IsOmega4MinusType L 1


end CFSG.GH74.QTGen4.DSGen4
