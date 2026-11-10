module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm6
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
public import CFSG.ClassicalInvolution.AschTight.MuZ2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]

structure Sec19Data {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G) : Prop where
  tight : S19R.TightStd p f K z
  mu : ¬ AllTypeTwo K z
  ih : CITBelowAll p (Nat.card G)
  cex : ¬ ConcOrTF4 G
  sylow : ∃ Q₀ : Sylow 2 K, (Q₀ : Subgroup K).map K.subtype ≤ (S : Subgroup G)
  hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)
  hW : W ∈ WSet (CoreAssembly.conjClass K)
  hWS : W ≤ (S : Subgroup G)


@[expose] def C19_14Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      W ⊔ centralizerModOdd (gammaGen (CoreAssembly.conjClass K) z) K ≠
        oddCoreOf (centralizerModOdd (gammaGen (CoreAssembly.conjClass K) z) K) ⊔ W

@[expose] def L6_11ModTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ S : Sylow 2 G, ∀ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) →
      ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (⨆ V ∈ η, V) ∈ η

@[expose] def L6_12ModTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
      ∀ S : Sylow 2 G,
        let M : Subgroup G := ⨆ U ∈ {U : Subgroup G | (∃ η ∈ etaG Ω, U ∈ η) ∧
          U ≤ (S : Subgroup G)}, U
        (∃ η ∈ etaG Ω, (∀ m ∈ M, ∀ U ∈ η, conjSub m U ∈ η) ∧
          (∀ η' ∈ etaG Ω, (∀ m ∈ M, ∀ U ∈ η', conjSub m U ∈ η') → η' = η) ∧
          ∀ g : G, (∀ U ∈ η, conjSub g U ≤ (S : Subgroup G)) → ∀ U ∈ η, conjSub g U ∈ η) ∨
        ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (S : Subgroup G) ∈ RSet Ω


@[expose] def InA {G : Type} [Group G] (Ω : Set (Subgroup G)) (K J : Subgroup G) : Prop :=
  J ∈ omegaStarNbr Ω K ∧ J ∉ omegaNbr Ω K ∧ ∃ zK zJ : G, IsUniqueInvolution K zK ∧
    IsUniqueInvolution J zJ ∧ ¬ ∃ g ∈ pairNormalizers K J zK zJ, conjSub g K = J

end CFSG.ClassicalInvolution.Disconnected.AschTight
