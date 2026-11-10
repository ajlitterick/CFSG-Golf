module

public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.Quasithin.Background.F918Z8g
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B1MoreTwelve
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.ASVolI.ChB

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Vocabulary

variable {V : Type*} [CommGroup V]

@[expose] def ActsTrivOnSection (g : MulAut V) (W U : Subgroup V) : Prop :=
  ∀ w ∈ W, g w * w⁻¹ ∈ U

@[expose] def autSec (X : Subgroup (MulAut V)) (W U : Subgroup V) :
    Subgroup (MulAut (↥W ⧸ U.subgroupOf W)) where
  carrier := {φ | ∃ g ∈ X, g ∈ stabSub W ∧ g ∈ stabSub U ∧
    ∀ w w' : ↥W, (w' : V) = g (w : V) →
      φ (QuotientGroup.mk w) = QuotientGroup.mk w'}
  one_mem' := by
    refine ⟨1, X.one_mem, (stabSub W).one_mem, (stabSub U).one_mem, ?_⟩
    intro w w' h
    have hw : w' = w := Subtype.ext h
    subst hw
    rfl
  mul_mem' := by
    rintro φ₁ φ₂ ⟨g₁, hg₁, hW₁, hU₁, h₁⟩ ⟨g₂, hg₂, hW₂, hU₂, h₂⟩
    refine ⟨g₁ * g₂, X.mul_mem hg₁ hg₂, (stabSub W).mul_mem hW₁ hW₂,
      (stabSub U).mul_mem hU₁ hU₂, ?_⟩
    intro w w' hw
    have hmem : g₂ (w : V) ∈ W := (mem_stabSub.1 hW₂ (w : V)).2 w.2
    have e₂ := h₂ w ⟨g₂ (w : V), hmem⟩ rfl
    have e₁ := h₁ ⟨g₂ (w : V), hmem⟩ w' (by simpa [MulAut.mul_apply] using hw)
    show φ₁ (φ₂ (QuotientGroup.mk w)) = _
    rw [e₂, e₁]
  inv_mem' := by
    rintro φ ⟨g, hg, hW, hU, h⟩
    refine ⟨g⁻¹, X.inv_mem hg, (stabSub W).inv_mem hW, (stabSub U).inv_mem hU, ?_⟩
    intro w w' hw
    have hw' : (w : V) = g (w' : V) := by
      rw [hw]; simp
    have e := h w' w hw'
    show φ.symm (QuotientGroup.mk w) = _
    rw [MulEquiv.symm_apply_eq]
    exact e.symm

end Vocabulary

section Groups

variable {M : Type*} [Group M]

@[expose] def IsIntDirProd {ι : Type*} (X : Subgroup M) (Gs : ι → Subgroup M) : Prop :=
  (∀ i j, i ≠ j → ∀ a ∈ Gs i, ∀ b ∈ Gs j, a * b = b * a) ∧ iSupIndep Gs ∧ (⨆ i, Gs i) = X

@[expose] def IsIntDirSum {ι : Type*} (X : Subgroup M) (Us : ι → Subgroup M) : Prop :=
  iSupIndep Us ∧ (⨆ i, Us i) = X

@[expose] def TwoChiefFactorsCentral (X : Subgroup M) : Prop :=
  ∀ N K : Subgroup M, N < K → K ≤ X → (N.subgroupOf X).Normal → (K.subgroupOf X).Normal →
    (∀ J : Subgroup M, N ≤ J → J ≤ K → (J.subgroupOf X).Normal → J = N ∨ J = K) →
    (∃ k : ℕ, N.relIndex K = 2 ^ k) → ⁅K, X⁆ ≤ N

@[expose] def fitOf (X : Subgroup M) : Subgroup M := CFSG.fittingSubgroupOf X

@[expose] def layerOf (X : Subgroup M) : Subgroup M := sSup {L | IsComponentOf L X}

@[expose] def oddCoreOf (X : Subgroup M) : Subgroup M := oddCoreIn X

@[expose] def conjSet (T K : Subgroup M) : Set (Subgroup M) :=
  {K' | ∃ t ∈ T, K' = K.map (MulAut.conj t).toMonoidHom}

@[expose] def conjClosureUnder (T K : Subgroup M) : Subgroup M := ⨆ K' ∈ conjSet T K, K'

end Groups

section FFNotation

variable {V : Type*} [CommGroup V]

@[expose] def offenderSet (G : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {A | IsFFStarOffender G A}

@[expose] def offenderStarSet (G : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {A | IsFFStarMin G A}

@[expose] def jStar (G : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ffJP (offenderStarSet G) G

@[expose] def fitJStar (G : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⁅fitOf G, jStar G⁆

end FFNotation

@[expose] def IsLieTypeQuasisimple (K : Type) [Group K] : Prop :=
  CFSG.Open.IsQuasisimple K ∧
    (CFSG.Blueprint.OddLieType (K ⧸ Subgroup.center K) ∨
      CFSG.Blueprint.EvenLieType (K ⧸ Subgroup.center K))

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement

@[expose] def B_1_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V),
      ((¬ ∃ A, IsA2 G A) ↔ Odd (Nat.card ↥G)) ∧ ((¬ ∃ A, IsA2 G A) → qOf G = ⊤)

section BurnsideB1a


end BurnsideB1a


@[expose] def B_1_2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V),
      (∀ A, IsA2 G A →
        ((rk (⊥ : Subgroup (MulAut V)) + rk (fixV (⊥ : Subgroup (MulAut V))) ≤
            rk A + rk (fixV A)) ↔ rkIdx (fixV A) ≤ rk A) ∧
        (rkIdx (fixV A) ≤ rk A ↔ rAV A ≤ 1)) ∧
      (∀ A, IsA2 G A → FFLe G A A) ∧
      (∀ A B, FFLe G B A → FFLe G A B → A = B) ∧
      (∀ A B C, FFLe G C B → FFLe G B A → FFLe G C A)


@[expose] def B_1_4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V),
      (∀ A, IsFFStarOffender G A → rAV A ≤ 1) ∧
      (∀ A B, IsFFStarOffender G A → FFLe G B A → IsFFStarOffender G B) ∧
      ((∀ A, IsFFStarMin G A → IsQuadratic A) ∧
        (∀ A, IsFFStarOffender G A →
          (∀ B, IsFFStarOffender G B → B ≤ A → B = A) → IsQuadratic A)) ∧
      ((∀ A, IsA2 G A → rAV A ≤ 1 → ∃ B, B ≤ A ∧ IsFFStarOffender G B ∧ rAV B ≤ 1) ∧
        (∀ A, IsA2 G A → rAV A < 1 → ∃ B, B ≤ A ∧ IsFFStarOffender G B ∧ rAV B < 1)) ∧
      ((IsFFModule G ↔ ∃ A, IsFFStarOffender G A) ∧
        ((∃ A, IsFFStarOffender G A) ↔ qOf G ≤ 1)) ∧
      (¬ IsStrongFFModule G →
        {A | IsFFStarOffender G A} = {A | IsA2 G A ∧ rAV A = 1})


@[expose] def B_1_5 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G A : Subgroup (MulAut V), IsFFStarOffender G A →
      (∀ W : Subgroup V, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → commSub W A ≠ ⊥ →
        IsFFStarOffender (autSub G W) (autSub A W) ∧
        (IsFFStarMin G A →
          IsFFStarMin (autSub G W) (autSub A W) ∧
            (¬ IsStrongFFStarOffender (autSub G W) (autSub A W) →
              W ⊔ fixV A = ⊤ ∧ A ⊓ centSub W = ⊥)) ∧
        (IsFFStarMin G A → qOf (autSub G W) = 1 →
          IsFFStarMin (autSub G W) (autSub A W) ∧ W ⊔ fixV A = ⊤ ∧ A ⊓ centSub W = ⊥) ∧
        (rk (autSub A W) = rkIdx (fixV (autSub A W)) →
          A ⊓ centSub W = ⊥ ∨ IsFFStarOffender G (A ⊓ centSub W)) ∧
        (A ⊓ centSub W = ⊥ → qOf (autSub G W) = 1 → W ⊔ fixV A = ⊤ ∧ commV A ≤ W)) ∧
      (IsFFStarMin G A → ∀ X : Subgroup (MulAut V), X ≤ G → twoResidual X = X → ⁅X, A⁆ = X →
        TwoChiefFactorsCentral X →
        ∀ I ∈ IrrPlus X ⊤, ∀ a ∈ A, I.map a.toMonoidHom = I) ∧
      (∀ L : Subgroup (MulAut V), IsComponentOf L G → A ≤ Subgroup.normalizer (L : Set (MulAut V))) ∧
      (CFSG.Open.IsQuasisimple ↥(quasithinGenFitting G) → pCoreOf 2 G = ⊥ →
        ∀ W U : Subgroup V, U ≤ W → (∀ g ∈ G, g ∈ stabSub W ∧ g ∈ stabSub U) →
          (∃ l ∈ quasithinGenFitting G, ¬ ActsTrivOnSection l W U) →
          ((∀ a ∈ A, ActsTrivOnSection a W U → a = 1) ∧ Nonempty (↥A ≃* ↥(ChB.autSec A W U)) ∧
              ∃ B, IsFFStarOffender (ChB.autSec G W U) B ∧ B ≤ ChB.autSec A W U) ∧
          (qOf (ChB.autSec G W U) = 1 →
            IsFFStarOffender (ChB.autSec G W U) (ChB.autSec A W U) ∧
              commSub U (A ⊔ quasithinGenFitting G) = ⊥ ∧ commV (A ⊔ quasithinGenFitting G) ≤ W ∧
              W ⊔ fixV A = ⊤))

section BurnsideB1b


end BurnsideB1b


@[expose] def B_1_7 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), IsFFModule G → IsStableFF G {A | IsFFStarMin G A}


@[expose] def B_1_8 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), pCoreOf 2 G = ⊥ → IsFFModule G → Group.IsSolvable ↥G →
      ∃ (s : ℕ) (Gs : Fin s → Subgroup (MulAut V)),
        IsIntDirProd (ffJ G) Gs ∧
        IsIntDirSum (commV (ffJ G)) (fun i => commV (Gs i)) ∧
        (∀ i, Nonempty (↥(Gs i) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∧
          ActsAsNaturalL2 (Gs i) (commV (Gs i))) ∧
        (qOf G = 1 ∧ ∀ A, ¬ IsStrongFFStarOffender G A) ∧
        (∀ A, IsFFStarOffender G A ↔ ∃ As : Fin s → Subgroup (MulAut V),
          (∀ i, As i = ⊥ ∨ IsSylowTwoOf (As i) (Gs i)) ∧ (∃ j, As j ≠ ⊥) ∧ A = ⨆ i, As i) ∧
        (∀ P : Set (Subgroup (MulAut V)), IsStableFF G P →
          (∃ I : Finset (Fin s), ffJP P G = ⨆ i ∈ I, Gs i) ∧
          (P ∩ offenderStarSet G = {A | A ∈ offenderStarSet G ∧ A ≤ ffJP P G}))

section BurnsideB1c


end BurnsideB1c


@[expose] def B_1_9 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), pCoreOf 2 G = ⊥ → fitJStar G ≠ ⊥ →
      ∃ (s : ℕ) (Gs : Fin s → Subgroup (MulAut V)),
        IsIntDirProd (ffJ G)
          (fun o : Option (Fin s) => o.elim
            (ffJP (offenderSet G) (G ⊓ Subgroup.centralizer (fitJStar G : Set (MulAut V)))) Gs) ∧
        (∀ i, Nonempty (↥(Gs i) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) ∧
        IsIntDirProd (fitJStar G) (fun i => oddCoreOf (Gs i)) ∧
        (∀ i, Nonempty (↥(oddCoreOf (Gs i)) ≃* Multiplicative (ZMod 3))) ∧
        IsIntDirProd (fitOf G)
          ![fitJStar G, fitOf G ⊓ Subgroup.centralizer (jStar G : Set (MulAut V))] ∧
        IsIntDirSum (commV (fitJStar G)) (fun i => commV (oddCoreOf (Gs i))) ∧
        (∀ i, commV (oddCoreOf (Gs i)) = commV (Gs i) ∧ Nat.card ↥(commV (Gs i)) = 2 ^ 2) ∧
        {A | A ∈ offenderStarSet G ∧ ⁅fitOf G, A⁆ ≠ ⊥} = {A | ∃ i, IsSylowTwoOf A (Gs i)} ∧
        (∀ A ∈ offenderStarSet G, ∀ K : Subgroup (MulAut V), K ≤ G → ⁅K, A⁆ = K →
          K ≤ jStar G ⊓ Subgroup.centralizer (fitOf G : Set (MulAut V)))


@[expose] def B_1_10 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), pCoreOf 2 G = ⊥ →
      ∀ K : Subgroup (MulAut V), K ≤ G → (∃ A, IsFFStarOffender G A ∧ ⁅K, A⁆ = K) →
        (CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) →
          K ≤ ffJ G ⊓ Subgroup.centralizer (fitOf G : Set (MulAut V))


@[expose] def B_1_11 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L A : Subgroup (MulAut V), IsFFStarOffender G A → L ≤ G →
      CFSG.Open.IsQuasisimple ↥L → ⁅L, A⁆ = L →
        ∃ (H : Subgroup (MulAut V)) (I : Subgroup V), L ≤ H ∧ H ≤ G ∧ I ∈ IrrPlus L ⊤ ∧
          (∀ h ∈ H, h ∈ stabSub I) ∧
          (∀ h ∈ H, h ∈ stabSub (fixV L ⊓ I)) ∧
          IsFFModule (ChB.autSec H I (fixV L ⊓ I)) ∧
          (∀ h ∈ H, ActsTrivOnSection h I (fixV L ⊓ I) → ∀ l ∈ L, h * l = l * h) ∧
          XMod.IsIrrSec ↥L (fixV L ⊓ I) I


@[expose] def B_1_12 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T K : Subgroup (MulAut V), IsSylowTwoOf T G → K ≤ G →
      Nonempty (↥K ≃* Multiplicative (ZMod 3)) → ⁅K, ffJ T⁆ = K → IsSubnormal K (T ⊔ K) →
      ∃ (n : ℕ) (Ks : Fin n → Subgroup (MulAut V)),
        Set.range Ks = conjSet T K ∧ IsIntDirProd (conjClosureUnder T K) Ks ∧
        ∃ Ms : Fin n → Subgroup (↥(ffJ T ⊔ conjClosureUnder T K) ⧸
            pCore 2 ↥(ffJ T ⊔ conjClosureUnder T K)),
          IsIntDirProd ⊤ Ms ∧
          (∀ i, ((Ks i).subgroupOf (ffJ T ⊔ conjClosureUnder T K)).map
              (QuotientGroup.mk' (pCore 2 ↥(ffJ T ⊔ conjClosureUnder T K))) =
            relPPrimeCore 2 (Ms i)) ∧
          (∀ i, Nonempty (↥(Ms i) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) ∧
          (∀ t ∈ T, ∀ i, ∃ j,
            (((Ms i).comap (QuotientGroup.mk' (pCore 2 ↥(ffJ T ⊔ conjClosureUnder T K)))).map
              (ffJ T ⊔ conjClosureUnder T K).subtype).map (MulAut.conj t).toMonoidHom =
            ((Ms j).comap (QuotientGroup.mk' (pCore 2 ↥(ffJ T ⊔ conjClosureUnder T K)))).map
              (ffJ T ⊔ conjClosureUnder T K).subtype) ∧
          (∀ i j, ∃ t ∈ T,
            (((Ms i).comap (QuotientGroup.mk' (pCore 2 ↥(ffJ T ⊔ conjClosureUnder T K)))).map
              (ffJ T ⊔ conjClosureUnder T K).subtype).map (MulAut.conj t).toMonoidHom =
            ((Ms j).comap (QuotientGroup.mk' (pCore 2 ↥(ffJ T ⊔ conjClosureUnder T K)))).map
              (ffJ T ⊔ conjClosureUnder T K).subtype)


@[expose] def B_1_13 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), CFSG.SectionRank.IsKGroupCat ↥G → pCoreOf 2 G = ⊥ →
      ∀ T K : Subgroup (MulAut V), IsSylowTwoOf T G → K ≤ G →
        (CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) → IsSubnormal K (K ⊔ T) →
        ⁅K, ffJP (offenderSet G) T⁆ = K →
          (Nonempty (↥K ≃* Multiplicative (ZMod 3)) ∧ K ≤ fitOf G ∧
              K ≤ Subgroup.centralizer (fitOf G : Set (MulAut V))) ∨
          (IsComponentOf K G ∧ (IsLieTypeQuasisimple ↥K ∨ (∃ n, IsAlt n ↥K) ∨
              IsHat ↥K ↥(alternatingGroup (Fin 6)))) ∨
          ∃ L : Subgroup (MulAut V), IsComponentOf L G ∧ K ≤ L ∧
            ∃ m, IsAlt m ↥L ∧ ((∃ n, n ≤ m ∧ IsAlt n ↥K) ∨ (IsPSL 3 2 1 ↥K ∧ m = 7))

end CFSG.ASVolI
