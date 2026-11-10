module

public import CFSG.Quasithin.Background.C4Statement
public import CFSG.Quasithin.H13.L32NA3SQTK
public import CFSG.Quasithin.Background.C41PfA
public import CFSG.Milestones.ASVolI.C1

public section

namespace CFSG.ASVolI.ChC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure HypC41 (H R M L V K : Subgroup G) : Prop where
  hyp : HypC28 H R M L V
  comp : K ∈ cComp H
  charTwo : CharTwo K
  quasi : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)
  not_le : ¬ K ≤ M

structure SetC41 (H R M L V T K : Subgroup G) : Prop where
  hyp : HypC41 H R M L V K
  sylow : IsSylowTwoOf T M
  le_T : R ≤ T
  red : H = conjClosure K H ⊔ conjClosure L M ⊔ T

@[expose] def C41Case1 (R M L V K : Subgroup G) : Prop :=
  ∃ n : ℕ, (n = 5 ∨ n = 6) ∧ IsAltBlockType (conjClosure L M) n ∧
    V = blockU (conjClosure L M) ∧ IsAltBlockType K (n + 2) ∧ InducesTransposition R K (n + 2) ∧
    M ⊓ K = K ⊓ Subgroup.normalizer (R : Set G)

@[expose] def C41Case2 (M L V K : Subgroup G) : Prop :=
  IsSp4Block K ∧
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥K →* ↥(StatedSp 2 F))
      (β : ↥(blockU K) →* Multiplicative (Fin 2 ⊕ Fin 2 → F)),
      Fintype.card F = 4 ∧ IsMatrixBlockTypeWith K (StatedSp 2 F) α β ∧
        IsFLineVia (blockU K) (V ⊔ blockZ K) β ∧ IsMaxParabolic2 K (M ⊓ K) ∧
        M ⊓ K = K ⊓ Subgroup.normalizer ((V ⊔ blockZ K : Subgroup G) : Set G) ∧
        IsPSL 2 2 2 (ModO2 (conjClosure L M))

@[expose] def C41Case3 (R M L V K : Subgroup G) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 < n ∧ Fintype.card F = 2 ^ n ∧
    Nonempty (ModO2 K ≃* ↥(StatedSL 3 F)) ∧ IsMSPair (K ⊔ R) R ∧
    (IsC134Case 1 (K ⊔ R) R K ∨ IsC134Case 2 (K ⊔ R) R K ∨ IsC134Case 3 (K ⊔ R) R K ∨
      IsC134Case 4 (K ⊔ R) R K) ∧
    IsMaxParabolic2 K (M ⊓ K) ∧ IsPSL 2 2 n (ModO2 (conjClosure L M)) ∧
    (IsStabilizedLineOfNatural F R M K V ∨
      (IsC134Case 2 (K ⊔ R) R K ∧ ∃ V₁ V₂ : Subgroup G,
        IsStabilizedLineOfNatural F R M K V₁ ∧ IsStabilizedLineOfNatural F R M K V₂ ∧
        V = V₁ ⊔ V₂))

@[expose] def C41Case4 (M L K : Subgroup G) : Prop :=
  (IsPSL 4 2 1 (ModO2 K) ∨ IsPSL 5 2 1 (ModO2 K)) ∧ IsParabolic2 K (M ⊓ K) ∧
    (IsPSL 3 2 1 (ModO2 (conjClosure L M)) ∨ IsPSL 4 2 1 (ModO2 (conjClosure L M)))

@[expose] def C41Concl (H R M L V K : Subgroup G) : Prop :=
  L = conjClosure L M ∧ conjClosure L M ≤ conjClosure K H ∧ conjClosure K H = K ∧
    (C41Case1 R M L V K ∨ C41Case2 M L V K ∨ C41Case3 R M L V K ∨ C41Case4 M L K)


@[expose] def C48Case1 (R L V : Subgroup G) : Prop :=
  ∃ n : ℕ, IsPSL 2 2 n (ModO2 L) ∧
    ((∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
        IsNaturalSection (L ⊔ R) V (V ⊓ Subgroup.centralizer (L : Set G))
          (R.subgroupOf (L ⊔ R)) (StatedSL 2 F)) ∨
      (n = 2 ∧ IsAltNaturalSection (L ⊔ R) V (V ⊓ Subgroup.centralizer (L : Set G))
        (R.subgroupOf (L ⊔ R)) 5) ∨
      (1 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
        IsSumOfNaturalModules (L ⊔ R) V (V ⊓ Subgroup.centralizer (L : Set G))
          (R.subgroupOf (L ⊔ R)) (StatedSL 2 F) false 2))

@[expose] def KDescribedC31C41 (H R M L V K : Subgroup G) : Prop :=
  (CFSG.Open.IsComponentOf K H ∧ C31Conclusion H R M L V K) ∨
    (K ∈ cComp H ∧ CharTwo K ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ ¬ K ≤ M ∧
      C41Concl H R M L V K)

end CFSG.ASVolI.ChC

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

@[expose] def C_4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V K : Subgroup G), HypC41 H R M L V K →
    C41Concl H R M L V K


section


end

@[expose] def C_4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), HypC41 H R M L V K →
    IsSylowTwoOf T M → R ≤ T →
    let X := conjClosure K H ⊔ conjClosure L M ⊔ T
    (conjClosure L M ⊔ T ≤ X ∧ X ≤ H) ∧
    HypC41 X R (M ⊓ X) L V K ∧
    SetC41 X R (M ⊓ X) L V T K ∧
    conjClosure L (M ⊓ X) = conjClosure L M ∧
    (C41Concl X R (M ⊓ X) L V K →
      conjClosure K H = conjClosure K X ∧ C41Concl H R M L V K)

@[expose] def C_4_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC41 H R M L V T K →
    ¬ conjClosure L M ≤ centralizerSection H (conjClosure K H) (pCoreOf 2 (conjClosure K H))

section


end

@[expose] def C_4_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC41 H R M L V T K →
    R ≤ Subgroup.normalizer (K : Set G)

@[expose] def C_4_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC41 H R M L V T K →
    R ≤ Subgroup.normalizer (K : Set G) →
    (conjClosure L M ≤ M ⊓ K ∧ ((conjClosure L M).subgroupOf (M ⊓ K)).Normal) ∧
    (conjClosure L M ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K) ≤
        (K ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K)) ⊓
          Subgroup.normalizer ((R ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K) :
            Subgroup G) : Set G) ∧
      (K ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K)) ⊓
          Subgroup.normalizer ((R ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K) :
            Subgroup G) : Set G) ≤
        (M ⊓ K) ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K)) ∧
    K = conjClosure K H

@[expose] def C_4_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC41 H R M L V T K →
    R ≤ Subgroup.normalizer (K : Set G) → conjClosure L M ≤ M ⊓ K → K = conjClosure K H →
    IsChiBlock2 H K → IsAltType K 7 ∧ C41Case1 R M L V K

@[expose] def C_4_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC41 H R M L V T K →
    R ≤ Subgroup.normalizer (K : Set G) → conjClosure L M ≤ M ⊓ K → K = conjClosure K H →
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      Nonempty (ModO2 K ≃* ↥(StatedSL 3 F))) →
    C41Case3 R M L V K

@[expose] def C_4_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V : Subgroup G), HypC28 H R M L V → M < H →
    L = conjClosure L M ∧
    ∃ K : Subgroup G, K ∈ cComp H ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ L ≤ K ∧
      (C48Case10 H R M L V K ∨
        ((C48Case1 R L V ∨ C48Case2 H R M L V K ∨ C48Case3 H R M L V K ∨
            C48Case4 H R M L V K ∨ C48Case5 H R M L V K ∨ C48Case6 H R M L V K ∨
            C48Case7 H R M L V K ∨ C48Case8 H R M L V K ∨ C48Case9 H R M L V K) ∧
          ¬ K ≤ M ∧ M ≤ Subgroup.normalizer (K : Set G) ∧ KDescribedC31C41 H R M L V K))

end CFSG.ASVolI
