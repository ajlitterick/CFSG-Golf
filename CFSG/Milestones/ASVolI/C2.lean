module

public import CFSG.Milestones.ASVolI.C1
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.Background.C213NonQHolds
public import CFSG.Quasithin.Background.C22PfI

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

@[expose] def C_2_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R : Subgroup G), IsTwoRadicalIn H R →
    {S : Subgroup G | IsMaxSignalizer H (H ⊓ Subgroup.normalizer (R : Set G)) S} = {R} ∧
    pCoreOf 2 H ≤ R


@[expose] def C_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R L : Subgroup G), IsSQTKIn H → IsTwoRadicalIn H R →
    L ∈ cComp H →
    ((R : Set G) ∩ ((L : Set G) * (centralizerSection H L (pCoreOf 2 L) : Set G)) =
      ((R ⊓ L : Subgroup G) : Set G) * (centralizerSection R L (pCoreOf 2 L) : Set G)) ∧
    (R ⊓ L = pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set G)) ∧
      R ⊓ L = pCoreOf 2 (L ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G)) ∧
      (R ⊓ L ≠ ⊥ → IsTwoRadicalIn L (R ⊓ L))) ∧
    (R ⊓ Subgroup.normalizer (L : Set G) =
        pCoreOf 2 ((L ⊔ (R ⊓ Subgroup.normalizer (L : Set G))) ⊓
          Subgroup.normalizer ((R ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) : Set G)) ∧
      (R ⊓ Subgroup.normalizer (L : Set G) ≠ ⊥ →
        IsTwoRadicalIn (L ⊔ (R ⊓ Subgroup.normalizer (L : Set G)))
          (R ⊓ Subgroup.normalizer (L : Set G)))) ∧
    ((CFSG.Blueprint.EvenLieType
        ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
      IsAlt 6 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
      IsPSU 3 3 1 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) →
      IsParabolic2 (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))
        (((L ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G)).subgroupOf L).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L))))

section


end

@[expose] def C_2_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L : Subgroup G), HypC23 H R M → L ∈ cComp H →
    CharTwo L → CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    (IsSylowTwoOf (R ⊓ L) L →
      (L ≤ M ∨ (IsChi0Block H L ∧
        (∃ V : Subgroup G, IsR2Max (L ⊔ (R ⊓ Subgroup.normalizer (L : Set G))) V ∧
          ∃ A : Subgroup G, A ≤ R ⊓ Subgroup.normalizer (L : Set G) ∧
            IsFFOffender (L ⊔ (R ⊓ Subgroup.normalizer (L : Set G))) V A) ∧
        IsBorelOfBlock L (L ⊓ M)))) ∧
    (IsSylowTwoOf (R ⊓ L) L ∨ R ≤ Subgroup.normalizer (L : Set G))

@[expose] def C_2_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M : Subgroup G), HypC23 H R M → IsSylowTwoOf R H →
    CharTwo H →
    ∃ Ls : List (Subgroup G), (∀ L ∈ Ls, IsChi0Block H L) ∧
      (H : Set G) = (M : Set G) * (Ls.map (fun L : Subgroup G => (L : Set G))).prod

section BurnsideC2b


end BurnsideC2b

section


end

@[expose] def C_2_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M : Subgroup G), HypC23 H R M →
    CharTwo (oTwoFIn H) →
    IsSylowTwoOf R (oTwoFIn H ⊔ R) ∧
    (¬ oTwoFIn H ≤ M →
      ∃ Ls : List (Subgroup G),
        (∀ L ∈ Ls, IsBlock2 (oTwoFIn H) L ∧ IsAltType L 3 ∧ ¬ L ≤ M) ∧
        (oTwoFIn H : Set G) = ((M ⊓ oTwoFIn H : Subgroup G) : Set G) *
          (Ls.map (fun L : Subgroup G => (L : Set G))).prod)

section


end

@[expose] def C_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M K V : Subgroup G), HypC23 H R M → K ∈ cComp H →
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → CharTwo K → ¬ K ≤ M →
    R ≤ Subgroup.normalizer (K : Set G) → V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) →
    (pCoreOf 2 (K ⊔ R) ≤ (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ∧
      (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K ∧
      IsTwoReducedIn (K ⊔ R) V) ∧
    (¬ thompsonJ R ≤ thompsonJ (pCoreOf 2 (K ⊔ R)) ∧
      ∃ hV : IsElemAbelian 2 V,
        @IsFFModule V (commGroupOfElemAbelian hV) (autOn (K ⊔ R) V) ∧
        ∃ A : Subgroup (MulAut ↥V), A ≤ autOn R V ∧
          @IsFFStarOffender V (commGroupOfElemAbelian hV) (autOn (K ⊔ R) V) A) ∧
    (
      (IsChiBlock2 H K ∧
        (
          ((∃ n : ℕ, 1 < n ∧ IsLin2Type K n) ∧
            IsSylowTwoOf (autOn (thompsonJ R) V) (autOn K V) ∧
            CFSG.Quasithin.IsBorelIn (autOn K V) (autOn (M ⊓ K) V)) ∨
          (IsAltType K 5 ∧ IsSylowTwoOf R (K ⊔ R) ∧
            Nonempty (↥(autOn (K ⊔ R) V) ≃* Equiv.Perm (Fin 5)) ∧
            CFSG.Quasithin.IsBorelIn (autOn K V) (autOn (M ⊓ K) V)) ∨
          (IsAltType K 7 ∧ Nonempty (↥(autOn R V) ≃* DihedralGroup 4) ∧
            ∃ (e : ↥(autOn (K ⊔ R) V) ≃* Equiv.Perm (Fin 7))
              (P : Finset (Finset (Fin 7))), IsPartitionOfType P {4, 3} ∧
              ((autOn (M ⊓ K) V).subgroupOf (autOn (K ⊔ R) V)).map e.toMonoidHom =
                MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7)) ∨
          (IsAltType K 7 ∧ IsE2 3 ↥(autOn R V) ∧
            ∃ (e : ↥(autOn (K ⊔ R) V) ≃* Equiv.Perm (Fin 7))
              (P : Finset (Finset (Fin 7))), IsPartitionOfType P {2, 2, 2, 1} ∧
              ((autOn (M ⊓ K) V).subgroupOf (autOn (K ⊔ R) V)).map e.toMonoidHom =
                MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7)))) ∨
      ((∃ (n : ℕ) (α : ↥K →* alternatingGroup (Fin n)), 5 ≤ n ∧ n ≤ 8 ∧ IsShort2 K ∧
          IsAltBlockTypeWith K n α ∧
          ∃ t : G, t ∈ R ∧ ∃ htV : t ∈ Subgroup.normalizer (V : Set G),
            autOn R V = Subgroup.zpowers (conjAct V ⟨t, htV⟩) ∧
            orderOf (conjAct V ⟨t, htV⟩) = 2 ∧
            ∃ σ : Equiv.Perm (Fin n), σ.IsSwap ∧
              ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
                ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
                  σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹) ∧
        autOn (M ⊓ K) V = autOn K V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V))) ∨
      (IsHatA6Block K ∧ M.relIndex K = 15 ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 4 ∧
          ∃ (ρ : ↥K →* Matrix.GeneralLinearGroup (Fin 3) F)
            (e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)),
            (∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * k⁻¹ →
              Multiplicative.toAdd (e v) =
                ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
                  (Multiplicative.toAdd (e u))) ∧
            ∃ W : Submodule F (Fin 3 → F), Module.finrank F W = 2 ∧
              ∀ k : ↥K, (k : G) ∈ M ↔ ∀ w ∈ W,
                ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w
                  ∈ W) ∨
      (IsExcA7Block K ∧ M.relIndex K = 35) ∨
      ((IsAltBlockType K 6 ∨ IsSp4Block K) ∧
        IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V)) ∨
      (IsG2Block K ∧ IsG2Two ↥(autOn (K ⊔ R) V) ∧
        IsMaxParabolic2 (autOn (K ⊔ R) V) (autOn (M ⊓ K) V ⊔ autOn R V)) ∨
      ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 ≤ n ∧ Fintype.card F = 2 ^ n ∧
          Nonempty (↥(autOn K V) ≃* ↥(StatedSL 3 F))) ∧
        IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V) ∧ IsMSPair (K ⊔ R) R) ∨
      ((Nonempty (↥(autOn K V) ≃* ↥(StatedSL 4 (ZMod 2))) ∨
          Nonempty (↥(autOn K V) ≃* ↥(StatedSL 5 (ZMod 2)))) ∧
        IsParabolic2 (autOn K V) (autOn (M ⊓ K) V) ∧
          ¬ CFSG.Quasithin.IsBorelIn (autOn K V) (autOn (M ⊓ K) V)))

@[expose] def C_2_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T : Subgroup G), HypC28 H R M L V →
    IsSylowTwoOf T M → R ≤ T →
    (conjSubgroupsBy M L = conjSubgroupsBy T L ∧
      (conjClosure L M = L ∨
        ∃ L₂ : Subgroup G, L₂ ∈ conjSubgroupsBy T L ∧ L₂ ≠ L ∧ conjClosure L M = L ⊔ L₂ ∧
          L ∈ cComp (conjClosure L M) ∧ L₂ ∈ cComp (conjClosure L M) ∧
          ⁅L, L₂⁆ ≤ pCoreOf 2 (conjClosure L M) ∧
          (L ⊔ pCoreOf 2 (conjClosure L M)) ⊓ (L₂ ⊔ pCoreOf 2 (conjClosure L M)) =
            pCoreOf 2 (conjClosure L M)) ∧
      ⁅conjClosure L M, conjClosure L M⁆ = conjClosure L M) ∧
    (conjClosure L M ≤ Subgroup.normalizer (R : Set G) ∧ IsTwoRadicalIn H R) ∧
    (∀ X : Subgroup G, conjClosure L M ⊔ T ≤ X → X ≤ H → HypC28 X R (M ⊓ X) L V)

section BurnsideC2c


end BurnsideC2c

section


end

@[expose] def C_2_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V : Subgroup G), HypC28 H R M L V →
    oddCoreIn H = ⊥ ∧
    (∀ K : Subgroup G, IsComponentOf K H → ¬ K ≤ M) ∧
    IsSylowTwoOf R (centralizerSection H (conjClosure L M) (pCoreOf 2 (conjClosure L M))) ∧
    HypC23 H R M ∧
    {S : Subgroup G | IsMaxSignalizer (H ⊓ Subgroup.normalizer (R : Set G))
      (conjClosure L M) S} = {R}


@[expose] def C_2_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V : Subgroup G), HypC28 H R M L V →
    oTwoFIn H ≤ M

section


end

@[expose] def C_2_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V : Subgroup G), HypC28 H R M L V →
    H ⊓ Subgroup.normalizer (conjClosure L M : Set G) = M

section


end

@[expose] def C_2_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V : Subgroup G), HypC28 H R M L V →
    oTwoFstarIn H ≤ M →
    (H = M ∨
      (conjClosure L M = L ∧ L ∈ cComp H ∧
        M = H ⊓ Subgroup.normalizer (conjClosure L M : Set G) ∧ M.relIndex H = 2))

section


end

@[expose] def C_2_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T H₁ : Subgroup G), HypC28 H R M L V →
    IsSylowTwoOf T M → R ≤ T → H₁ ≤ H → Group.IsSolvable ↥H₁ →
    conjClosure L M ⊔ T ≤ Subgroup.normalizer (H₁ : Set G) → H₁ ≤ M

section


end

end CFSG.ASVolI
