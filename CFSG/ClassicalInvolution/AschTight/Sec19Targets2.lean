module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement MatrixGroups

section Vocabulary

variable {G : Type} [Group G]

abbrev sec19X (K : Subgroup G) (z : G) : Subgroup G :=
  gammaGen (CoreAssembly.conjClass K) z

abbrev sec19Y (K : Subgroup G) (z : G) : Subgroup G :=
  centralizerModOdd (sec19X K z) K

@[expose] def IsSL2ModOdd (H : Subgroup G) (m : ℕ) : Prop :=
  ∃ (p' e : ℕ) (_ : Fact p'.Prime), p' ≠ 2 ∧ 0 < e ∧ p' ^ e = m ∧
    Nonempty (↥H ⧸ classicalInvolutionOddCore ↥H ≃* SL(2, GaloisField p' e))

structure IsSL2Three (H N : Subgroup G) (m : ℕ) : Prop where
  le : N ≤ H
  normal : H ≤ Subgroup.normalizer (N : Set G)
  sl2 : IsSL2ModOdd N m
  cyclic : ∃ h ∈ H, IsPGroup 2 (Subgroup.zpowers h) ∧ N ⊔ Subgroup.zpowers h = H
  wreathed : ∀ P : Subgroup G, IsSylow2In P H → IsWreathed P

structure HypOmegaGen (Ω : Set (Subgroup G)) : Prop where
  conjInvariant : ConjInvariant Ω
  omega1 : ∀ K ∈ Ω, (∃ z : G, IsUniqueInvolution K z) ∧
    ∃ P : Subgroup G, IsSylow2In P K ∧ ¬ IsMulCommutative ↥P
  omega2 : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)} = K ∨
    Nonempty (↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, ZMod 3))
  omega3 : ∀ K ∈ Ω, ∀ J ∈ Ω, ∀ P Q : Subgroup G, IsSylow2In P K → IsSylow2In Q J →
    Nat.card ↥P = Nat.card ↥Q
  omega4 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J →
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J)
  omega5 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → ∀ z : G, IsUniqueInvolution K z → ∀ v ∈ J,
    (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
      v ∈ Subgroup.normalizer (K : Set G)

end Vocabulary

variable (p f : ℕ) [Fact p.Prime]

structure Sec19DataT {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G) : Prop extends Sec19Data p f K z S W where
  memL : L ∈ CoreAssembly.conjClass K
  invL : IsUniqueInvolution L t
  ne : t ≠ z
  memV : V ∈ USet (CoreAssembly.conjClass K)
  leW : V ≤ W
  memT : t ∈ V


@[expose] def C19_8Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G), Sec19DataT p f K z S W L t V →
      let A := (S : Subgroup G) ⊓
        Subgroup.centralizer (((S : Subgroup G) ⊓ K ⊔ Subgroup.zpowers t : Subgroup G) : Set G)
      let B := W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G)
      A = centralizerModOdd A L ⊔ B ∧ Disjoint (centralizerModOdd A L) B ∧
        ∀ a ∈ centralizerModOdd A L, ∀ b ∈ B, a * b = b * a


@[expose] def C19_11Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      (S : Subgroup G) ⊓ centralizerModOdd ⊤ (sec19X K z) ≤ W


end CFSG.ClassicalInvolution.Disconnected.AschTight
