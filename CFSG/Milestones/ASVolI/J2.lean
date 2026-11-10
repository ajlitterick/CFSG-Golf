module

public import CFSG.Milestones.ASVolI.I8
public import CFSG.Quasithin.Background.ASVolIRu.Bridge
public import CFSG.Quasithin.Background.ASVolIRu.StUnique
public import CFSG.Quasithin.Recognition.RuTypeJ210d
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section Diag

variable (K : Type) [Field K]

@[expose] noncomputable def conjSL (M : GL (Fin 2) K) : SL(2, K) →* SL(2, K) where
  toFun A := ⟨(M : Matrix (Fin 2) (Fin 2) K) * A *
    ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
      ← Matrix.det_mul]
    simp⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' A B := by
    apply Subtype.ext
    have h : ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (M : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    show (M : Matrix (Fin 2) (Fin 2) K) * ((A : Matrix (Fin 2) (Fin 2) K) * B) *
        ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((M : Matrix (Fin 2) (Fin 2) K) * A * ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
        ((M : Matrix (Fin 2) (Fin 2) K) * B * ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    simp only [mul_assoc]
    rw [← mul_assoc ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      (M : Matrix (Fin 2) (Fin 2) K), h, one_mul]

theorem conjSL_central (M : GL (Fin 2) K) (A : SL(2, K)) (hA : A ∈ Subgroup.center SL(2, K)) :
    conjSL K M A = A := by
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  apply Subtype.ext
  show (M : Matrix (Fin 2) (Fin 2) K) * A * ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = A
  rw [← hr, ← (Matrix.scalar_commute r (fun _ => Commute.all _ _)
    (M : Matrix (Fin 2) (Fin 2) K)).eq, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    mul_one]

@[expose] noncomputable def conjPSL (M : GL (Fin 2) K) : PSL(2, K) →* PSL(2, K) :=
  QuotientGroup.map (Subgroup.center SL(2, K)) (Subgroup.center SL(2, K)) (conjSL K M)
    (fun x hx => by rw [Subgroup.mem_comap, conjSL_central K M x hx]; exact hx)

end Diag

section Ru

variable {G : Type} [Group G]

@[expose] def S0Ru (L B7 : Subgroup G) : Subgroup G := SRu L ⊓ Subgroup.centralizer (B7 : Set G)

@[expose] def InducesTranspositionOn (g : G) (X : Subgroup G) : Prop :=
  g ∈ Subgroup.normalizer (X : Set G) ∧
    ∃ (e : ↥X ⧸ Subgroup.center ↥X ≃* alternatingGroup (Fin 6)) (τ : Equiv.Perm (Fin 6)),
      τ.IsSwap ∧ ∀ x y : ↥X, (y : G) = g⁻¹ * x * g →
        ((e (y : ↥X ⧸ Subgroup.center ↥X) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
          τ * ((e (x : ↥X ⧸ Subgroup.center ↥X) : alternatingGroup (Fin 6)) :
            Equiv.Perm (Fin 6)) * τ⁻¹

@[expose] def InducesDiagonalOn (g : G) (X : Subgroup G) : Prop :=
  g ∈ Subgroup.normalizer (X : Set G) ∧
    ∃ (e : ↥X ⧸ Subgroup.center ↥X ≃* PSL(2, GaloisField 3 2))
      (M : GL (Fin 2) (GaloisField 3 2)),
      ¬ IsSquare (Matrix.GeneralLinearGroup.det M) ∧
      ∀ x y : ↥X, (y : G) = g⁻¹ * x * g →
        e (y : ↥X ⧸ Subgroup.center ↥X) = conjPSL (GaloisField 3 2) M (e (x : ↥X ⧸ Subgroup.center ↥X))

end Ru

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def J_2_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    T ≤ L ∧
    (ZRu T = V ⊓ Subgroup.centralizer (T : Set G) ∧ Nat.card ↥(ZRu T) = 2)

section BurnsideJ1_2146


end BurnsideJ1_2146


@[expose] def J_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    (HRu T ⊓ L = L1Ru L T ⊔ T ∧ QRu T ⊔ SRu L = pCoreOf 2 (L1Ru L T ⊔ T) ∧
      pCoreOf 2 (L1Ru L T ⊔ T) = R1Ru L T ∧ QRu T ≤ KRu T) ∧
    (IsElemAbelian 2 (URu V T) ∧ Nat.card ↥(URu V T) = 32) ∧
    ((∀ x : G, x ∈ HCRu V T ↔
        (x ∈ QRu T ∧ ∀ k ∈ KRu T, x⁻¹ * k⁻¹ * x * k ∈ URu V T)) ∧
      ∃ (_ : ((QRu T).subgroupOf (KRu T)).Normal)
        (e : ↥(KRu T) ⧸ (QRu T).subgroupOf (KRu T) ≃* Matrix.SpecialLinearGroup (Fin 2) F4),
        IsConjModuleIso (KRu T) (QRu T) (HCRu V T) (Fin 2 → F4)
          (fun k v => ((e (k : ↥(KRu T) ⧸ (QRu T).subgroupOf (KRu T)) :
            Matrix.SpecialLinearGroup (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4).mulVec v)) ∧
    (∀ t : ↥(URu V T) ≃* ↥(URu V T),
      (∀ u : ↥(URu V T), (t u : G) * (u : G)⁻¹ ∈ ZRu T) ↔
        ∃ q ∈ QRu T, ∀ u : ↥(URu V T), (t u : G) = q⁻¹ * u * q) ∧
    (∀ l ∈ L, CFSG.conjugate (URu V T) l ≠ URu V T →
      Nat.card ↥(((CFSG.conjugate (URu V T) l).subgroupOf (HRu T)).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(HRu T)))) = 2 ∧
        V = CFSG.conjugate (URu V T) l ⊓ HCRu V T)

@[expose] def J_2_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ B B7 : Subgroup G, IsSylowIn 3 B (L1Ru L T) → B7 ≤ L → Nat.card ↥B7 = 7 →
      B ≤ Subgroup.normalizer (B7 : Set G) →
      ∀ z s : G, Subgroup.zpowers z = ZRu T → s ∈ S0Ru L B7 → s ≠ 1 →
        (S0Ru L B7 = ⁅S0Ru L B7, B⁆ ∧ IsElemAbelian 2 (S0Ru L B7) ∧
          Nat.card ↥(S0Ru L B7) = 4) ∧
        (∀ g : G, g⁻¹ * z * g ∉ S0Ru L B7) ∧
        (Subgroup.centralizer ({s} : Set G) ⊓ L =
            S0Ru L B7 ⊔ ⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆ ⊔ B7 ∧
          IsDirectProductOf (S0Ru L B7) ⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆
            (SRu L ⊓ Subgroup.centralizer ({s} : Set G)) ∧
          IsSylowTwoIn (SRu L ⊓ Subgroup.centralizer ({s} : Set G))
            (Subgroup.centralizer ({s} : Set G) ⊓ L) ∧
          Nat.card ↥(SRu L ⊓ Subgroup.centralizer ({s} : Set G)) = 2 ^ 8 ∧
          Monoid.exponent ↥(SRu L ⊓ Subgroup.centralizer ({s} : Set G)) = 4) ∧
        (B ≤ Subgroup.normalizer ((SRu L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) ∧
          B ≤ Subgroup.normalizer ((S0Ru L B7 : Subgroup G) : Set G) ∧
          B ≤ Subgroup.normalizer
            ((⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆ : Subgroup G) : Set G)) ∧
        (IsSuzukiTwoGroup ↥⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆ ∧
          ∃ a ∈ ⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆,
            ∃ b ∈ ⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆, a * b ≠ b * a) ∧
        (∀ t ∈ SRu L, t ∉ V →
          ⁅Subgroup.zpowers t, SRu L⁆ = V ∧
          V.relIndex (SRu L ⊓ Subgroup.centralizer ({t} : Set G)) = 2 ^ 5) ∧
        Nonempty (↥(QRu T ⊓ Subgroup.centralizer (B : Set G)) ≃* QuaternionGroup 2) ∧
        (∀ x : G, x ∈ URu V T ↔ (x ∈ SRu L ∧ ∀ r ∈ R1Ru L T, x⁻¹ * r⁻¹ * x * r ∈ V)) ∧
        (∀ l ∈ L, l ∉ HRu T → URu V T ⊓ CFSG.conjugate (URu V T) l = V)

section BurnsideJ2b


end BurnsideJ2b


section BurnsideJ3b

section Transport

variable {G : Type} [Group G]


end Transport

section TwoResidual

variable {G : Type} [Group G]


end TwoResidual

section Sylow

variable {G : Type} [Group G]


end Sylow

section Ident

variable {G : Type} [Group G]


end Ident

section Pair

variable {G : Type} [Group G] [Finite G]


end Pair

section Parts

variable {G : Type} [Group G] [Finite G]


end Parts

section Conj

variable {G : Type} [Group G] [Finite G]


end Conj

end BurnsideJ3b


@[expose] def J_2_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ h ∈ HCRu V T, h ∉ URu V T →
      ⁅Subgroup.zpowers h, QRu T⁆ ⊔ ZRu T = URu V T ∧
      ⁅Subgroup.zpowers h, QRu T⁆ = URu V T ∧
      QRu T ⊓ Subgroup.centralizer ({h} : Set G) = Subgroup.zpowers h ⊔ URu V T


@[expose] def J_2_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ B : Subgroup G, IsSylowIn 3 B (L1Ru L T) →
      Nonempty (↥(QRu T ⊓ Subgroup.centralizer (B : Set G)) ≃* QuaternionGroup 2) ∧
      ∃ (_ : (B.subgroupOf (HRu T ⊓ Subgroup.centralizer (B : Set G))).Normal),
        Nonempty (↥(HRu T ⊓ Subgroup.centralizer (B : Set G)) ⧸
          B.subgroupOf (HRu T ⊓ Subgroup.centralizer (B : Set G)) ≃* SemidihedralGroup 4)


@[expose] def J_2_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ z : G, Subgroup.zpowers z = ZRu T →
      ((∀ i ∈ involutionsOf (HRu T), i ∉ KRu T → ∀ j ∈ involutionsOf (HRu T), j ∉ KRu T →
          ∃ h ∈ HRu T, j = h⁻¹ * i * h) ∧
        (involutionsOf (HRu T) \ (KRu T : Set G)).ncard = 640 ∧
        (∀ i ∈ involutionsOf (HRu T), i ∉ KRu T → i ∈ conjClass z)) ∧
      (∀ i ∈ involutionsOf L, i ∉ SRu L → i ∈ conjClass z) ∧
      (∀ i ∈ involutionsOf (QRu T), i ∈ conjClass z) ∧
      (URu V T = omegaOne (HCRu V T) ∧ ZRu T = frattiniOf (HCRu V T) ∧
        ∀ u ∈ URu V T, u ≠ 1 → u ∈ conjClass z)


@[expose] def J_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ B B7 : Subgroup G, IsSylowIn 3 B (L1Ru L T) → B7 ≤ L → Nat.card ↥B7 = 7 →
      B ≤ Subgroup.normalizer (B7 : Set G) →
      ∀ z s : G, Subgroup.zpowers z = ZRu T → s ∈ S0Ru L B7 → s ≠ 1 →
        IsHatCover ↥(LBRu B) (alternatingGroup (Fin 6)) ∧
        (∃ (_ : (B.subgroupOf (Subgroup.centralizer (B : Set G))).Normal),
          Nonempty (↥(Subgroup.centralizer (B : Set G)) ⧸
            B.subgroupOf (Subgroup.centralizer (B : Set G)) ≃*
            ↥(NativeSporadic.M11 ⊓
              MulAction.stabilizer (Equiv.Perm (Fin 11)) (0 : Fin 11)))) ∧
        (∃ (_ : (B.subgroupOf (Subgroup.normalizer (B : Set G))).Normal),
          Nonempty (↥(Subgroup.normalizer (B : Set G)) ⧸
            B.subgroupOf (Subgroup.normalizer (B : Set G)) ≃*
            MulAut (alternatingGroup (Fin 6)))) ∧
        ((∀ i ∈ involutionsOf (⊤ : Subgroup G), i ∈ conjClass s ∨ i ∈ conjClass z) ∧
          s ∉ conjClass z) ∧
        (∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) →
          Subgroup.centralizer (B5 : Set G) =
            pCoreOf 5 (Subgroup.centralizer (B5 : Set G)) ⊔
              (QRu T ⊓ Subgroup.centralizer (B5 : Set G)) ∧
          Nonempty (↥(QRu T ⊓ Subgroup.centralizer (B5 : Set G)) ≃* QuaternionGroup 2) ∧
          Nat.card ↥(pCoreOf 5 (Subgroup.centralizer (B5 : Set G))) = 5 ^ 3 ∧
          ∀ g : G, ¬ IsSylowIn 5 (CFSG.conjugate B5 g) (LBRu B)) ∧
        ((∀ i ∈ involutionsOf (LBRu B), i ∈ conjClass z) ∧
          (∀ i ∈ involutionsOf (⊤ : Subgroup G), InducesTranspositionOn i (LBRu B) →
            i ∈ conjClass z) ∧
          (∀ i ∈ involutionsOf (⊤ : Subgroup G), InducesDiagonalOn i (LBRu B) →
            i ∈ conjClass s)) ∧
        ((∃ a ∈ involutionsOf (KRu T), a ∉ QRu T ∧ ∃ b ∈ involutionsOf (KRu T), b ∉ QRu T ∧
            (∀ i ∈ involutionsOf (KRu T), i ∉ QRu T →
              (∃ h ∈ HRu T, i = h⁻¹ * a * h) ∨ (∃ h ∈ HRu T, i = h⁻¹ * b * h)) ∧
            (¬ ∃ h ∈ HRu T, b = h⁻¹ * a * h) ∧ a ∈ conjClass s ∧ b ∈ conjClass z) ∧
          (∀ x ∈ HRu T, x ∈ conjClass s → ∃ h ∈ HRu T, x = h⁻¹ * s * h) ∧
          (∀ x ∈ HRu T, x ∈ conjClass s → x ∈ KRu T ∧ x ∉ QRu T) ∧
          (conjClass z ∩ ((KRu T : Set G) \ (QRu T : Set G))).ncard = 480) ∧
        (∀ i ∈ involutionsOf (Subgroup.centralizer (B : Set G)), i ∈ conjClass z) ∧
        (S0Ru L B7 ⊔ ⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆ =
            HRu T ⊓ Subgroup.centralizer ({s} : Set G) ∧
          IsSylowTwoIn (HRu T ⊓ Subgroup.centralizer ({s} : Set G))
            (Subgroup.centralizer ({s} : Set G))) ∧
        (∀ x y : G, orderOf x = 3 → orderOf y = 3 → ∃ g : G, y = g⁻¹ * x * g)


@[expose] def J_2_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ z : G, Subgroup.zpowers z = ZRu T →
      ((∀ i ∈ involutionsOf (QRu T), i ∉ URu V T → ∀ j ∈ involutionsOf (QRu T), j ∉ URu V T →
          ∃ h ∈ HRu T, j = h⁻¹ * i * h) ∧
        (involutionsOf (QRu T) \ (URu V T : Set G)).ncard = 240 ∧
        (∀ i ∈ involutionsOf (QRu T), i ∉ URu V T → i ∈ conjClass z)) ∧
      (∀ i ∈ involutionsOf (SRu L ⊓ QRu T), ∃ l ∈ L, l⁻¹ * i * l ∈ URu V T) ∧
      (∀ u ∈ URu V T, u ∉ V →
        ∀ i ∈ involutionsOf (SRu L ⊓ Subgroup.centralizer ({u} : Set G)), i ∈ conjClass z)

section BurnsideJ28a

section BurnsideJ28Two8


end BurnsideJ28Two8

end BurnsideJ28a


@[expose] def J_2_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ B B7 : Subgroup G, IsSylowIn 3 B (L1Ru L T) → B7 ≤ L → Nat.card ↥B7 = 7 →
      B ≤ Subgroup.normalizer (B7 : Set G) →
      ∀ z s : G, Subgroup.zpowers z = ZRu T → s ∈ S0Ru L B7 → s ≠ 1 →
        (IsDirectProductOf (S0Ru L B7) (LsRu s) (Subgroup.centralizer ({s} : Set G)) ∧
          SuzukiModel ↥(LsRu s) 2 3) ∧
        (Subgroup.normalizer ((S0Ru L B7 : Subgroup G) : Set G) =
            Subgroup.centralizer ({s} : Set G) ⊔ B ∧
          InducesOuterAutomorphisms B (LsRu s)) ∧
        conjClass z ∩ (Subgroup.centralizer ({s} : Set G) : Set G) = involutionsOf (LsRu s)

section BurnsideJ4_2910


end BurnsideJ4_2910

section


end

@[expose] def J_2_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ B B7 : Subgroup G, IsSylowIn 3 B (L1Ru L T) → B7 ≤ L → Nat.card ↥B7 = 7 →
      B ≤ Subgroup.normalizer (B7 : Set G) →
      ∀ s : G, s ∈ S0Ru L B7 → s ≠ 1 →
        ∀ p : ℕ, (p = 7 ∨ p = 13) → ∀ Y : Subgroup G, IsSylowIn p Y (LsRu s) →
          (IsSylowIn p Y ⊤ ∧ Nat.card ↥Y = p) ∧
          Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer ((S0Ru L B7 : Subgroup G) : Set G) ∧
          (Y ⊔ S0Ru L B7 = Subgroup.centralizer (Y : Set G) ∧
            ∃ (_ : ((Subgroup.centralizer (Y : Set G)).subgroupOf
                (Subgroup.normalizer (Y : Set G))).Normal),
              IsCyclic (↥(Subgroup.normalizer (Y : Set G)) ⧸
                (Subgroup.centralizer (Y : Set G)).subgroupOf (Subgroup.normalizer (Y : Set G))) ∧
              Nat.card (↥(Subgroup.normalizer (Y : Set G)) ⧸
                (Subgroup.centralizer (Y : Set G)).subgroupOf (Subgroup.normalizer (Y : Set G))) =
                p - 1)

section


end

end CFSG.ASVolI
