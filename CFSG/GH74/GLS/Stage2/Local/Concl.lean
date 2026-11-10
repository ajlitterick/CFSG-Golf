module

public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.GH74.GLS.Bg.Statements

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12
open scoped commutatorElement Matrix MatrixGroups

section Vocab

variable {G : Type} [Group G]

@[expose] def IsClassicalKind (k : Kind) : Prop := k = Kind.psp4 ∨ ∃ ε : Bool, k = Kind.l4 ε

@[expose] def G2Three (z : G) (S : Subgroup G) : Prop :=
  ∃ (r₁ : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), G2Shape z S r₁ 3 L₁ L₂

@[expose] def G2Big (z : G) (S : Subgroup G) : Prop :=
  ∃ (r₁ r₂ : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), 3 < r₂ ∧ G2Shape z S r₁ r₂ L₁ L₂

@[expose] def IsQuat (Y : Type) [Group Y] : Prop := ∃ n : ℕ, IVK.IsQuaternionTwoGroup Y n

@[expose] def IsL34Two (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* CFSG.GH74.GLS.Bg.TwoGroups.SylSL3_4)


@[expose] def HasTwoInvolutionClasses (Y : Type) [Group Y] : Prop :=
  ∃ x y : Y, orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y

end Vocab

section P21

variable {G : Type} [Group G]


@[expose] def Prop21h (z : G) : Prop :=
  ∃ V : Subgroup G, V ≤ LC z ∧ IVK.IsFourSubgroup V ∧
    (AutOrd (Cen z) V = 3 ∨ AutOrd (Cen z) V = 6)

@[expose] def Prop22a (z : G) (S : Subgroup G) : Prop :=
  (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) → ¬ IsMulCommutative ↥S →
    ∀ U : Subgroup G, U ≤ S → IVK.IsFourSubgroup U → (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) →
      z ∈ U ∧ AutOrd (⊤ : Subgroup G) U = 6

@[expose] def Prop22x [Finite G] (z : G) (S : Subgroup G) : Prop :=
  ∀ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1Pair G z S q L₁ L₂ →
    ∀ t ∈ S, IsConj z t → Swaps z t L₁ L₂ → z ∈ ⁅LC z, zpowers t⁆

end P21

section L23

variable {G : Type} [Group G]

@[expose] def Lemma23e (z : G) (k : Kind) (S : Subgroup G) : Prop :=
  ∀ U : Subgroup G, U ≤ S → IVK.IsFourSubgroup U → (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) →
    U ≤ LC z ⊓ ⁅Cen z, U⁆ ∧
    (k ≠ Kind.m12 → (k = Kind.g2 → G2Big z S) → LC z ≤ ⁅Cen z, U⁆ ⊔ OddCore z)

@[expose] def Lemma23 (z : G) (k : Kind) (S : Subgroup G) : Prop :=
  ((RC S z).relIndex S ≤ 4 ∧ ((RC S z).relIndex S = 4 → ∃ ε : Bool, k = Kind.l4 ε)) ∧
  (RC S z = S → k = Kind.mcl ∨ k = Kind.ly) ∧
  (RC S z ≠ S → ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) ∧
  2 ≤ pRank 2 ↥(⁅Cen z, Cen z⁆ : Subgroup G) ∧
  Lemma23e z k S

@[expose] def Lemma26 (z : G) (S : Subgroup G) : Prop :=
  pLayerOf 2 (Cen z) ⊔ (S ⊓ WC z) ≤
    ⨆ (t : G) (_ : t ∈ S) (_ : IsConj z t), O2Of ⁅Cen z, zpowers t⁆

end L23

section P27

variable {G : Type} [Group G] [Finite G]


end P27

section L29

variable {G : Type} [Group G]

@[expose] def Lemma29b (U : Subgroup G) : Prop :=
  ∃ (Q Xg : Subgroup G) (v : G),
    CFSG.ABGLocalTools.IsSylowOf 2 Q (O22Of (centralizer (U : Set G))) ∧ v * v = 1 ∧
    (∃ x : G, Xg = zpowers x ∧ IsPGroup 3 ↥Xg ∧
      x ∈ normalizer (Q : Set G) ⊓ centralizer (U : Set G) ∧
      x ^ 3 ∈ pPrimeCoreOf 2 (centralizer (U : Set G))) ∧
    (∀ c ∈ centralizer (U : Set G), ∃ o ∈ pPrimeCoreOf 2 (centralizer (U : Set G)), ∃ q ∈ Q,
      ∃ a ∈ Xg, ∃ b ∈ zpowers v, c = o * q * a * b) ∧
    ⁅Q, Xg⁆ = Q ∧ IsL34Two ↥Q ∧ Q ⊓ centralizer (Xg : Set G) = U ∧
    CFSG.ABGLocalTools.IsSylowOf 2 U (centralizer (Q : Set G)) ∧
    (QuotIso (centralizer (U : Set G)) (O22Of (centralizer (U : Set G))) (Multiplicative (ZMod 3)) ∨
      QuotIso (centralizer (U : Set G)) (O22Of (centralizer (U : Set G))) (Equiv.Perm (Fin 3)))


end L29

section Sec3

variable {G : Type} [Group G]

abbrev Hat (K : Subgroup G) : Type := ↥K ⧸ pPrimeCore 2 ↥K


end Sec3

section Sec3b

variable {G : Type} [Group G] [Finite G]

@[expose] def Prop34Concl (z : G) (k : Kind) (S : Subgroup G) (H : Subgroup G) : Prop :=
  (∀ h ∈ H, ∃ c ∈ Cen z, ∃ o ∈ pPrimeCoreOf 2 H, h = c * o) ∨
    IsDihedral ↥S ∨
    (∃ (ε : Bool) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)),
      k = Kind.l4 ε ∧ Stage1L4 G z S ε q L₁ L₂ ∧ q % 4 = (if ε then 3 else 1) ∧ 3 < q ∧
      IVK.IsPSp4 ↥(generalizedFitting (HBar H)) q ∧ IsCoatom (barIn H (Cen z)) ∧
      barIn H (LC z) ≤ generalizedFitting (HBar H) ∧ ¬ barIn H S ≤ generalizedFitting (HBar H) ∧
      O2Of H ≠ H ∧ CFSG.GH74.GLS.Bg.Fm (barIn H (Cen z)) = barIn H (zpowers z))


end Sec3b


end CFSG.GH74.GLS.Stage2.Local
