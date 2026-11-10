module

public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

class DSLeaf (L : Prop) : Prop where
  holds : L


theorem faithful_a5 [DSLeaf LeafFaithfulA5] {G : Type} [Group G] [Finite G] {P L E K : Subgroup G} (hLP : L ≤ P) (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hEP : E ≤ P) (hPE : P ≤ Subgroup.normalizer (E : Set G)) (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hsec : IsElemSec K E) (hcard : K.relIndex E ≤ 16) (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hcore : ∀ q ∈ pCoreOf 2 P, ∀ e ∈ E, ⁅q, e⁆ ∈ K) (hnt : ∃ l ∈ L, ∃ e ∈ E, ⁅l, e⁆ ∉ K) :
    A5Chief P L E K :=
  DSLeaf.holds (L := LeafFaithfulA5) hLP hPL hEP hPE hPK hsec hcard hq hcore hnt

theorem m2 [DSLeaf LeafM2] {G : Type} [Group G] [Finite4 G] {L P S : Subgroup G} (h : A5Par L P) (hS : IsSylowTwoOf S P) (hQS : pCoreOf 2 P ≤ S) :
    (pCoreOf 2 P).relIndex S ∣ 8 ∧ Odd ((pCoreOf 2 P).relIndex (dsCentMod P L (pCoreOf 2 P))) ∧
      (∀ d ∈ P ⊓ Subgroup.normalizer (S : Set G), orderOf d = 3 → (pCoreOf 2 P).relIndex S = 4) :=
  DSLeaf.holds (L := LeafM2) h hS hQS

theorem m3 [DSLeaf LeafM3] {G : Type} [Group G] [Finite G] {P L E K T : Subgroup G} (h : A5Chief P L E K) (hT : IsSylowTwoOf T L) :
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
          FixFree (⁅⁅E, T⁆, T⁆ ⊔ K) (⁅E, T⁆ ⊔ K) d)) :=
  DSLeaf.holds (L := LeafM3) h hT

theorem m4 [DSLeaf LeafM4] {G : Type} [Group G] [Finite G] {P L E K T X Y : Subgroup G} (h : A5Chief P L E K) (hT : IsSylowTwoOf T L) (hX : X ≤ T ⊔ pCoreOf 2 P) (hq : ⁅⁅E, X⁆, X⁆ ≤ K) (hnt : ¬ ⁅E, X⁆ ≤ K) (hfaith : ∀ x ∈ X, (∀ e ∈ E, ⁅x, e⁆ ∈ K) → x ∈ pCoreOf 2 P) (hKY : K ≤ Y) (hYE : Y ≤ E) (hYc : ∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈ K) (hcard : Y.relIndex E ≤ (X ⊓ pCoreOf 2 P).relIndex X) :
    NatSec L K E ∧ X ⊔ pCoreOf 2 P = T ⊔ pCoreOf 2 P ∧ Y.relIndex E = 4 :=
  DSLeaf.holds (L := LeafM4) h hT hX hq hnt hfaith hKY hYE hYc hcard

theorem m5 [DSLeaf LeafM5] {G : Type} [Group G] [Finite G] {L T : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) :
    (∀ X : Subgroup G, pCoreOf 2 L ≤ X → X ≤ T →
        L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G) →
          X = pCoreOf 2 L ∨ X = T) ∧
      (∀ d ∈ L ⊓ Subgroup.normalizer (T : Set G), orderOf d = 3 → FixFree (pCoreOf 2 L) T d) :=
  DSLeaf.holds (L := LeafM5) hq hT


theorem omega4_minus_of_orth [DSLeaf LeafOmega4MinusOfOrth] {G : Type} [Group G] [Finite G] {L : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hc : CharTwo L) (he : IsElemAbelian 2 (pCoreOf 2 L)) (hn : Nat.card (pCoreOf 2 L) = 16) (hnat : ¬ NatSec L ⊥ (pCoreOf 2 L)) :
    IsOmega4MinusType L 1 :=
  DSLeaf.holds (L := LeafOmega4MinusOfOrth) hq hc he hn hnat


end CFSG.GH74.QTGen4.DSGen4
