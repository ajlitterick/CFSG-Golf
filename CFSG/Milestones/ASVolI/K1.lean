module

public import CFSG.Milestones.ASVolI.I8
public import CFSG.Quasithin.Background.SmithB42Alt6
public import CFSG.Quasithin.Background.SmithB45Alt6
public import CFSG.Quasithin.Background.SmithB45HatA6
public import CFSG.Quasithin.EmptyFaithful.LRed14B45
public import CFSG.Quasithin.Background.SmithB42Alt7
public import CFSG.Quasithin.Background.SmithB45Alt7
public import CFSG.Quasithin.Background.SmithB45Exc3A7
public import CFSG.Quasithin.Background.SmithB45L2Main
public import CFSG.Quasithin.Background.SmithB45U3Nat
public import CFSG.Quasithin.Background.SmithB45Sp4Main
public import CFSG.Quasithin.Background.HSU3NPrime
public import CFSG.Quasithin.Background.SmithB45U33Main
public import CFSG.Quasithin.Background.SmithB45G2Main
public import CFSG.Quasithin.Background.SmithB42G2Main
public import CFSG.Quasithin.Background.SmithC27RTypeU33
public import CFSG.Quasithin.H13.L32A753d
public import CFSG.Quasithin.Background.SmithB42Dispatch
public import CFSG.Quasithin.Background.SmithB45Tits
public import CFSG.Quasithin.Background.SmithB45D4
public import CFSG.Quasithin.Background.SmithB42LnL42
public import CFSG.Quasithin.Background.SmithB42LnL52
public import CFSG.Quasithin.H13.A5Quad8
public import CFSG.Quasithin.Background.SmithB45LnL4Main
public import CFSG.Quasithin.Background.SmithB45LnL5Main
public import CFSG.Quasithin.Background.SmithB45SL3L32
public import CFSG.Quasithin.Background.SmithB45SL3Even
public import CFSG.Quasithin.Background.SmithB42SL3Even
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113DetMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeList
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.Quasithin.Background.B1More13
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Quasithin.Background.HTriSolv
public import CFSG.Quasithin.Background.SmithB51SL3M
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146A2
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.H13.A5S1520a
public import CFSG.Quasithin.H13.A5S1520c
public import CFSG.Quasithin.H13.A5S1520d
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.H13.L32A753b
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Sporadic.J4.QT2LocMain
public import CFSG.Sporadic.J4.QT2LocRadMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped MatrixGroups

structure KSetupBase (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)) : Prop where
  elem2 : ∀ v : V, v ^ 2 = 1
  hyp : B4Hyp G L

structure KSetup (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)) : Prop where
  elem2 : ∀ v : V, v ^ 2 = 1
  hyp : B4Hyp G L
  qhat : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)

abbrev qc (c : ℚ) : WithTop ℚ := (c : WithTop ℚ)

abbrev Lbar {V : Type} [CommGroup V] (L : Subgroup (MulAut V)) : Type := ↥L ⧸ Subgroup.center ↥L

@[expose] def IsSLn (n q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧ Nonempty (X ≃* ↥(StatedSL n K))

@[expose] def IsSp4F (q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧ Nonempty (X ≃* ↥(StatedSp 2 K))

@[expose] def IsG2Derived (r : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ r ∧
    Nonempty (X ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆)

section Vocab2

variable {V : Type} [CommGroup V]

@[expose] def oTwoPrimeRes {X : Type} [Group X] (G : Subgroup X) : Subgroup X :=
  Subgroup.closure {g | g ∈ G ∧ ∃ k : ℕ, g ^ (2 ^ k) = 1}

@[expose] def TrivialOnDynkin {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (G L : Subgroup (MulAut V)) (Γ : Subgroup (Matrix.GeneralLinearGroup ι F)) : Prop :=
  ∃ π : ↥Γ →* ↥L, Function.Surjective π ∧ ∀ g ∈ G,
    ∃ (A : Matrix.GeneralLinearGroup ι F) (φ : F ≃+* F), ∀ x : ↥Γ, ∃ y : ↥Γ,
      ((y : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) =
        (A : Matrix ι ι F) * (((x : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).map φ) *
          ((A⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) ∧
      ((π y : ↥L) : MulAut V) = g * ((π x : ↥L) : MulAut V) * g⁻¹

@[expose] def EndIsF2 (L : Subgroup (MulAut V)) : Prop :=
  ∀ φ : V →* V, (∀ l ∈ L, ∀ v : V, φ (l v) = l (φ v)) → φ = 1 ∨ φ = MonoidHom.id V

@[expose] def Rt (T L : Subgroup (MulAut V)) (t : MulAut V) : Subgroup (MulAut V) :=
  Subgroup.centralizer ({t} : Set (MulAut V)) ⊓ (T ⊓ L)

@[expose] def Xt (T L : Subgroup (MulAut V)) (t : MulAut V) : Subgroup (MulAut V) :=
  Rt T L t ⊔ Subgroup.zpowers t

structure OrthogonalFourCoordinates (L : Subgroup (MulAut V)) (s : ℕ)
    (F : Type) [Field F] [Finite F] [CharP F 2] where
  field_card : Nat.card F = 2 ^ (2 * s)
  group_equiv : ↥(StatedSL 2 F) ≃* ↥L
  module_equiv : V ≃* ↥(hermSub s (Fin 2) F)
  intertwines : ∀ groupElement vector,
    ((module_equiv (((group_equiv groupElement : ↥L) : MulAut V) vector) :
      Multiplicative (Matrix (Fin 2) (Fin 2) F))) =
        twistAct s (StatedSL 2 F) groupElement
          (module_equiv vector : Multiplicative (Matrix (Fin 2) (Fin 2) F))

namespace OrthogonalFourCoordinates

variable {L : Subgroup (MulAut V)} {s : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] def matrix (coordinates : OrthogonalFourCoordinates L s F) (vector : V) :
    Matrix (Fin 2) (Fin 2) F :=
  Multiplicative.toAdd (coordinates.module_equiv vector :
    Multiplicative (Matrix (Fin 2) (Fin 2) F))

@[expose] def IsFixedScalar (s : ℕ) (scalar : F) : Prop := scalar ^ 2 ^ s = scalar

@[expose] def IsPoint (coordinates : OrthogonalFourCoordinates L s F)
    (vectors : Subgroup V) : Prop :=
  ∃ point : V, point ≠ 1 ∧ ∀ vector : V,
    vector ∈ vectors ↔ ∃ scalar : F, IsFixedScalar s scalar ∧
      coordinates.matrix vector = scalar • coordinates.matrix point

@[expose] def polar (coordinates : OrthogonalFourCoordinates L s F)
    (first second : V) : F :=
  (coordinates.matrix first + coordinates.matrix second).det -
    (coordinates.matrix first).det - (coordinates.matrix second).det

end OrthogonalFourCoordinates

end Vocab2

section MarkedGeometry

variable {V : Type} [CommGroup V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] def planeUnipotent (Γ : Subgroup (Matrix.GeneralLinearGroup ι F))
    (W : Submodule F (ι → F)) : Subgroup ↥Γ :=
  Subgroup.closure {g | (∀ v ∈ W,
    (((g : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec v) = v) ∧
    ∀ v, (((g : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec v) - v ∈ W}

@[expose] def markedPlaneImage (L : Subgroup (MulAut V))
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι F)) (π : ↥Γ →* ↥L)
    (W : Submodule F (ι → F)) : Subgroup (MulAut V) :=
  ((planeUnipotent Γ W).map π).map L.subtype

@[expose] def TrivialOnDynkinVia (G L : Subgroup (MulAut V))
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι F)) (π : ↥Γ →* ↥L) : Prop :=
  Function.Surjective π ∧ ∀ g ∈ G,
    ∃ (matrix : Matrix.GeneralLinearGroup ι F) (φ : F ≃+* F), ∀ x : ↥Γ, ∃ y : ↥Γ,
      ((y : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) =
        (matrix : Matrix ι ι F) * (((x : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).map φ) *
          ((matrix⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) ∧
      ((π y : ↥L) : MulAut V) = g * ((π x : ↥L) : MulAut V) * g⁻¹

@[expose] def IsSp4IsotropicPlane (W : Submodule F ((Fin 2 ⊕ Fin 2) → F)) : Prop :=
  Module.finrank F W = 2 ∧ ∀ v ∈ W, ∀ w ∈ W,
    (∑ index : Fin 2, (v (Sum.inl index) * w (Sum.inr index) -
      v (Sum.inr index) * w (Sum.inl index))) = 0

end MarkedGeometry

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open


@[expose] def K_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    (IsAlt 6 (Lbar L) ∨ IsAlt 7 (Lbar L)) →
    (IsAlt 6 ↥L ∨ IsHat ↥L ↥(alternatingGroup (Fin 6)) ∨ IsAlt 7 ↥L) ∧
    ((AlternatingNatural L ⊤ ⊥ 6 ∨ AlternatingNatural L ⊤ ⊥ 7) →
      (∀ A, IsFFStarOffender G A → B42Case3 G L ∨ B42Case5 G A ∨ B42Case6 G L A) ∧
      ((AlternatingNatural L ⊤ ⊥ 7 ∧ G = L) →
        qOf G = qc (3 / 2) ∧ qhatOf G = qc (3 / 2)))

section BurnsideKA


end BurnsideKA

section


end

@[expose] def K_1_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    IsAlt 6 ↥L →
    Nat.card V = 2 ^ 4 ∧ AlternatingNatural L ⊤ ⊥ 6 ∧
      ∀ A, IsFFStarOffender G A → B42Case3 G L ∨ B42Case6 G L A


@[expose] def K_1_2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    IsAlt 7 ↥L →
    (Nat.card V = 2 ^ 4 ∨ Nat.card V = 2 ^ 6) ∧
    (Nat.card V = 2 ^ 6 → AlternatingNatural L ⊤ ⊥ 7) ∧
    (Nat.card V = 2 ^ 4 → G = L ∧ A7Four L ⊤ ⊥ ∧
      (∀ T, IsSylowTwoOf T G →
        ∃ R, IsFFStarOffender T R ∧ ∀ A, IsFFStarOffender T A → A = R) ∧
      ∀ A, IsFFStarOffender G A → B42Case7 G L A)


@[expose] def K_1_3 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    IsHat ↥L ↥(alternatingGroup (Fin 6)) →
    Nat.card V = 2 ^ 6 ∧ TripleA6Six L ⊤ ⊥ ∧ (L.subgroupOf G).index ≤ 2 ∧
    (∀ T, IsSylowTwoOf T G →
      ∃ R, IsFFStarOffender T R ∧ ∀ A, IsFFStarOffender T A → A = R) ∧
    ∀ A, IsFFStarOffender G A → B42Case8 G L A


@[expose] def K_2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetupBase V G L →
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      (IsPSL 2 p 1 (Lbar L) ∨ IsPSL 2 p 2 (Lbar L) ∨ IsPSL 3 p 1 (Lbar L) ∨
        IsPSU 3 p 1 (Lbar L))) →
    ¬ IsAlt 6 (Lbar L) → ¬ IsPSL 2 2 2 (Lbar L) → ¬ IsPSL 3 2 1 (Lbar L) → ¬ IsPSU 3 3 1 (Lbar L) →
    ((2 : ℚ) : WithTop ℚ) < qhatOf G

section BurnsideKE


end BurnsideKE

section


end

@[expose] def K_3_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    ∀ r : ℕ, IsPSL 2 2 r (Lbar L) →
      IsSimpleGroup ↥L ∧ IsSLn 2 (2 ^ r) ↥L ∧ Nat.card V = 2 ^ (2 * r) ∧
      (BinaryNaturalSL L ⊤ ⊥ 2 r ∨ ∃ s, r = 2 * s ∧ BinaryOrthogonalFour L ⊤ ⊥ s)

section BurnsideKB


end BurnsideKB


@[expose] def K_3_1_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    ∀ r : ℕ, IsPSL 2 2 r (Lbar L) → BinaryNaturalSL L ⊤ ⊥ 2 r →
      (∀ T, IsSylowTwoOf T G →
        IsFFStarOffender T (T ⊓ L) ∧ ∀ A, IsFFStarOffender T A → A = T ⊓ L) ∧
      qOf G = qc 1 ∧ ∀ A, IsFFStarOffender G A → B42Case1 G L A


@[expose] def K_3_1_2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    ∀ s : ℕ, IsPSL 2 2 (2 * s) (Lbar L) → BinaryOrthogonalFour L ⊤ ⊥ s →
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
          (coordinates : OrthogonalFourCoordinates L s F),
        0 < s ∧ Nat.card V = 2 ^ (4 * s) ∧
        (∃ singularPoint : Subgroup V, coordinates.IsPoint singularPoint ∧
          ∀ vector ∈ singularPoint, (coordinates.matrix vector).det = 0) ∧
        (∀ singularSpace : Subgroup V,
          (∀ vector ∈ singularSpace, (coordinates.matrix vector).det = 0) →
          (∀ scalar : F, OrthogonalFourCoordinates.IsFixedScalar s scalar →
            ∀ vector ∈ singularSpace, ∀ scalarVector : V,
              coordinates.matrix scalarVector = scalar • coordinates.matrix vector →
                scalarVector ∈ singularSpace) → Nat.card singularSpace ≤ 2 ^ s) ∧
        ∀ T, IsSylowTwoOf T G →
          (∃ t : MulAut V,
            t ∈ Subgroup.normalizer (L : Set (MulAut V)) ∧
            t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)) ∧
            t ∉ L ∧ t ^ 2 = 1) ∧
        ∀ t : MulAut V,
          t ∈ Subgroup.normalizer (L : Set (MulAut V)) →
          t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)) →
          t ∉ L → t ^ 2 = 1 →
          (∀ vector, (coordinates.matrix (t vector)).det = (coordinates.matrix vector).det) ∧
          (∀ scalar : F, OrthogonalFourCoordinates.IsFixedScalar s scalar →
            ∀ first second : V, coordinates.matrix second = scalar • coordinates.matrix first →
              coordinates.matrix (t second) = scalar • coordinates.matrix (t first)) ∧
          (∃ fieldMatrix : Matrix.GeneralLinearGroup (Fin 2) F,
            (∀ groupElement : ↥(StatedSL 2 F),
              ∃ imageElement : ↥(StatedSL 2 F),
                ((imageElement : Matrix.GeneralLinearGroup (Fin 2) F) :
                    Matrix (Fin 2) (Fin 2) F) =
                  (fieldMatrix : Matrix (Fin 2) (Fin 2) F) *
                    frobPow s ((groupElement : Matrix.GeneralLinearGroup (Fin 2) F) :
                      Matrix (Fin 2) (Fin 2) F) *
                    (fieldMatrix⁻¹ : Matrix (Fin 2) (Fin 2) F) ∧
                ((coordinates.group_equiv imageElement : ↥L) : MulAut V) =
                  t * ((coordinates.group_equiv groupElement : ↥L) : MulAut V) * t⁻¹) ∧
            ∀ vector : V, coordinates.matrix (t vector) =
              (fieldMatrix : Matrix (Fin 2) (Fin 2) F) *
                frobPow s (coordinates.matrix vector) *
                  Matrix.transpose (frobPow s (fieldMatrix : Matrix (Fin 2) (Fin 2) F))) ∧
          (∃ point : V, point ≠ 1 ∧ (coordinates.matrix point).det ≠ 0 ∧
            ∀ vector : V, coordinates.matrix (t vector) = coordinates.matrix vector +
              (coordinates.polar vector point / (coordinates.matrix point).det) •
                coordinates.matrix point) ∧
          coordinates.IsPoint (commV (Subgroup.zpowers t)) ∧
          (∀ vector ∈ commV (Subgroup.zpowers t), vector ≠ 1 →
            (coordinates.matrix vector).det ≠ 0) ∧
          (∀ groupElement ∈ L,
            groupElement ∈ Subgroup.centralizer ({t} : Set (MulAut V)) ↔
              ∀ vector : V, vector ∈ commV (Subgroup.zpowers t) ↔
                groupElement vector ∈ commV (Subgroup.zpowers t)) ∧
          (∃ (K : Type) (_ : Field K) (_ : Finite K)
              (field_embedding : K →+* F), Nat.card K = 2 ^ s ∧
            Function.Injective field_embedding ∧
            (∀ scalar : F, OrthogonalFourCoordinates.IsFixedScalar s scalar ↔
              ∃ baseScalar : K, field_embedding baseScalar = scalar) ∧
            Nonempty (↥(L ⊓ Subgroup.centralizer ({t} : Set (MulAut V))) ≃*
              ↥(StatedSL 2 K))) ∧
          (∃ perpendicular : Subgroup V,
            (∀ vector : V, vector ∈ perpendicular ↔
              ∀ point ∈ commV (Subgroup.zpowers t), coordinates.polar vector point = 0) ∧
            (∀ scalar : F, OrthogonalFourCoordinates.IsFixedScalar s scalar →
              ∀ vector ∈ perpendicular, ∀ scalarVector : V,
                coordinates.matrix scalarVector = scalar • coordinates.matrix vector →
                  scalarVector ∈ perpendicular) ∧
            Nat.card perpendicular = 2 ^ (3 * s) ∧
            (∀ groupElement ∈ L ⊓ Subgroup.centralizer ({t} : Set (MulAut V)),
              ∀ vector ∈ perpendicular, groupElement vector ∈ perpendicular ∧
                (coordinates.matrix (groupElement vector)).det = (coordinates.matrix vector).det) ∧
            (∀ groupElement ∈ L ⊓ Subgroup.centralizer ({t} : Set (MulAut V)),
              (∀ vector ∈ perpendicular, groupElement vector = vector) → groupElement = 1) ∧
            (∀ isometry : MulAut ↥perpendicular,
              (∀ vector : ↥perpendicular,
                (coordinates.matrix (isometry vector : V)).det =
                  (coordinates.matrix (vector : V)).det) →
              (∀ scalar : F, OrthogonalFourCoordinates.IsFixedScalar s scalar →
                ∀ first second : ↥perpendicular,
                  coordinates.matrix (second : V) = scalar • coordinates.matrix (first : V) →
                    coordinates.matrix (isometry second : V) =
                      scalar • coordinates.matrix (isometry first : V)) →
              ∃ groupElement ∈ L ⊓ Subgroup.centralizer ({t} : Set (MulAut V)),
                ∀ vector : ↥perpendicular, groupElement (vector : V) = (isometry vector : V))) ∧
          (1 < s →
            (∀ element ∈ T ⊓ L, element ≠ 1 →
              ∃ normalizerElement ∈ L ⊓
                  Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)),
                element ∈ (Rt T L t).map (MulAut.conj normalizerElement).toMonoidHom) ∧
            (∀ first ∈ L ⊓ Subgroup.normalizer
                ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)),
              ∀ second ∈ L ⊓ Subgroup.normalizer
                ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)),
              (Rt T L t).map (MulAut.conj first).toMonoidHom =
                  (Rt T L t).map (MulAut.conj second).toMonoidHom ∨
                Disjoint ((Rt T L t).map (MulAut.conj first).toMonoidHom)
                  ((Rt T L t).map (MulAut.conj second).toMonoidHom)) ∧
            (∀ element ∈ T ⊓ L, element ∉ Rt T L t →
              coordinates.IsPoint (fixV (Rt T L t ⊔ Subgroup.zpowers element))))) ∧
      (s = 1 →
        (IsAlt 5 ↥G ∨ Nonempty (↥G ≃* Equiv.Perm (Fin 5))) ∧ AlternatingNatural L ⊤ ⊥ 5 ∧
        (Nonempty (↥G ≃* Equiv.Perm (Fin 5)) → ∀ A, IsFFStarOffender G A → B42Case5 G A) ∧
        (IsAlt 5 ↥G → qOf G ≤ qc 2 ∧ qhatOf G ≤ qc (3 / 2))) ∧
      (1 < s →
        ¬ IsFFModule G ∧
        (∀ T, IsSylowTwoOf T G → ∀ t : MulAut V,
          t ∈ Subgroup.normalizer (L : Set (MulAut V)) →
          t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)) →
          t ∉ L → t ^ 2 = 1 →
            (IsQuadratic (Xt T L t) ∧ Nat.card (fixV (Xt T L t)) = 2 ^ (2 * s) ∧
              rAV (Xt T L t) = ((2 * s : ℕ) : ℚ) / ((s : ℚ) + 1) ∧ rAV (Rt T L t) = 2) ∧
            ∀ A, IsA2 L A → A ≤ T ⊓ L →
              (∀ n ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)),
                ¬ A ≤ (Rt T L t).map (MulAut.conj n).toMonoidHom) →
              (3 / 2 : ℚ) ≤ rAV A ∧ (rAV A = 3 / 2 ↔ A = T ⊓ L) ∧
                commSeries A 3 = ⊥ ∧ ¬ IsQuadratic A) ∧
        (Odd (L.relIndex G) → qOf G = qc 2 ∧ qhatOf G = qc (3 / 2)) ∧
        ((∃ t ∈ G, t ∉ L ∧ t ^ 2 = 1) →
          qOf G = qc (((2 * s : ℕ) : ℚ) / ((s : ℚ) + 1)) ∧ qhatOf G ≤ qc (3 / 2) ∧
          ∀ T, IsSylowTwoOf T G → ∀ t ∈ T, t ∉ L → t ^ 2 = 1 →
            (∀ A ∈ Qset G, ∃ g ∈ G,
              A ≤ (Xt T L t).map (MulAut.conj g).toMonoidHom) ∧
            (∀ A ∈ Qset G,
              (∀ B ∈ Qset G, A ≤ B → B = A) →
                ∃ g ∈ G, A = (Xt T L t).map (MulAut.conj g).toMonoidHom))) ∧
      (qOf G ≤ qc 2 ∧ qhatOf G ≤ qc (3 / 2))


@[expose] def K_3_2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    ∀ n r : ℕ, 3 ≤ n → IsPSL n 2 r (Lbar L) →
      (n = 3 ∨ ((n = 4 ∨ n = 5) ∧ r = 1)) ∧
      ((IsSimpleGroup ↥L ∧ IsSLn n (2 ^ r) ↥L) ∨
        (n = 3 ∧ Even r ∧ (IsSLn 3 (2 ^ r) ↥L ∨ IsPSL 3 2 r ↥L))) ∧
      (BinaryNaturalSL L ⊤ ⊥ n r ∨
        (n = 4 ∧ r = 1 ∧ Nat.card V = 2 ^ 6 ∧ EndIsF2 L) ∨
        (n = 5 ∧ r = 1 ∧ Nat.card V = 2 ^ 10 ∧ EndIsF2 L) ∨
        (∃ s, r = 2 * s ∧ n = 3 ∧ BinaryNineTensor L ⊤ ⊥ s)) ∧
      (L < oTwoPrimeRes G →
        (n = 4 ∧ r = 1 ∧ Nat.card V = 2 ^ 6) ∨
        (n = 3 ∧ Even r ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ r ∧
          TrivialOnDynkin G L (StatedSL 3 F)))

section BurnsideKC


section


end


section


end

section


end


section


end


section Conj

variable {W : Type*} [CommGroup W]


end Conj


end BurnsideKC

section


end

@[expose] def K_3_2_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    ∀ n r : ℕ, 3 ≤ n → IsPSL n 2 r (Lbar L) → BinaryNaturalSL L ⊤ ⊥ n r →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ r ∧
        TrivialOnDynkin G L (StatedSL n F)) ∧
      qOf G = qc (1 / ((n : ℚ) - 1)) ∧
      (∀ T, IsSylowTwoOf T G → ∀ A, IsFFStarOffender T A → A ≤ L) ∧
      ∀ A, IsFFStarOffender G A → B42Case2 G L ∨ B42Case9 G L

section


end

@[expose] def K_3_2_2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    IsPSL 4 2 1 (Lbar L) → Nat.card V = 2 ^ 6 →
      SLExteriorTwo L ⊤ ⊥ 4 ∧ AlternatingNatural L ⊤ ⊥ 8 ∧
      ∀ A, IsFFStarOffender G A → B42Case10 G L A

section


end

@[expose] def K_3_2_3 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    IsPSL 5 2 1 (Lbar L) → Nat.card V = 2 ^ 10 →
      G = L ∧ EndIsF2 L ∧ SLExteriorTwo L ⊤ ⊥ 5 ∧
      (∀ T, IsSylowTwoOf T G →
        ∃ X, IsFFStarOffender T X ∧ rk ↥X = 4 ∧ rk ↥(fixV X) = 6 ∧ rAV X = 1 ∧
          ∀ A, IsFFStarOffender T A → A = X) ∧
      ∀ A, IsFFStarOffender G A → B42Case11 G L A

section


end

@[expose] def K_3_2_4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    ∀ s : ℕ, 1 ≤ s → IsPSL 3 2 (2 * s) (Lbar L) → BinaryNineTensor L ⊤ ⊥ s →
      Nat.card V = 2 ^ (9 * s) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ (2 * s) ∧
        TrivialOnDynkin G L (StatedSL 3 F)) ∧
      qc 2 < qOf G ∧ qhatOf G = qc (5 / 4) ∧
      ∀ T, IsSylowTwoOf T G →
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
          (π : ↥(StatedSL 3 F) →* ↥L) (W : Submodule F (Fin 3 → F))
          (X : Subgroup (MulAut V)),
          Nat.card F = 2 ^ (2 * s) ∧
          (FFModel.twistTensor s (StatedSL 3 F)).RealizesVia L ⊤ ⊥ π ∧
          TrivialOnDynkinVia G L (StatedSL 3 F) π ∧ Module.finrank F W = 2 ∧
          X = markedPlaneImage L (StatedSL 3 F) π W ∧
          IsA2 T X ∧ rk ↥X = 4 * s ∧ rk ↥(fixV X) = 4 * s ∧
          rAV X = 5 / 4 ∧ commSeries X 3 = ⊥ ∧
          ∀ A, IsA2 T A → rAV A ≤ 5 / 4 → A = X


@[expose] def K_3_3 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    ∀ s : ℕ, IsPSU 3 2 s (Lbar L) →
      2 ≤ s ∧ CFSG.Quasithin.IsSU3 (2 ^ s) ↥L ∧ (Even s → IsSimpleGroup ↥L) ∧
      (Odd s → Nat.card (Subgroup.center ↥L) = 3) ∧
      BinaryNaturalSU3 L ⊤ ⊥ s ∧ Nat.card V = 2 ^ (6 * s) ∧
      (∀ T, IsSylowTwoOf T G →
        rk ↥(ChIJK.omegaOne (T ⊓ L)) = s ∧ rk ↥(fixV (ChIJK.omegaOne (T ⊓ L))) = 4 * s ∧
          rAV (ChIJK.omegaOne (T ⊓ L)) = 2 ∧ Qset T = {ChIJK.omegaOne (T ⊓ L)}) ∧
      qOf G = qc 2 ∧ qhatOf G = qc 2

section BurnsideKD


end BurnsideKD

section


end

@[expose] def K_3_4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    ∀ r : ℕ, 1 < r → IsPSp4 2 r (Lbar L) →
      IsSp4F (2 ^ r) ↥L ∧
      (BinaryNaturalSp4 L ⊤ ⊥ r ∨ ∃ s, r = 2 * s ∧ TwistedTensorSp4 L ⊤ ⊥ s)

section


end

@[expose] def K_3_4_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    ∀ r : ℕ, 1 < r → IsPSp4 2 r (Lbar L) → BinaryNaturalSp4 L ⊤ ⊥ r →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ r ∧
        TrivialOnDynkin G L (StatedSp 2 F)) ∧
      (∀ T, IsSylowTwoOf T G →
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
          (π : ↥(StatedSp 2 F) →* ↥L) (W : Submodule F ((Fin 2 ⊕ Fin 2) → F))
          (X : Subgroup (MulAut V)),
          Nat.card F = 2 ^ r ∧ (FFModel.nat (StatedSp 2 F)).RealizesVia L ⊤ ⊥ π ∧
          TrivialOnDynkinVia G L (StatedSp 2 F) π ∧ IsSp4IsotropicPlane W ∧
          X = markedPlaneImage L (StatedSp 2 F) π W ∧ IsA2 T X ∧ IsQuadratic X ∧
          rk ↥X = 3 * r ∧ rk ↥(fixV X) = 2 * r ∧ rAV X = 2 / 3) ∧
      (∀ A, IsFFStarOffender G A → A ≤ L) ∧
      qOf G = qc (2 / 3) ∧ ∀ A, IsFFStarOffender G A → B42Case3 G L


@[expose] def K_3_4_2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    ∀ s : ℕ, 1 ≤ s → IsPSp4 2 (2 * s) (Lbar L) → TwistedTensorSp4 L ⊤ ⊥ s →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ (2 * s) ∧
        TrivialOnDynkin G L (StatedSp 2 F)) ∧
      Nat.card V = 2 ^ (16 * s) ∧ qhatOf G = qc 2 ∧ qc 2 < qOf G ∧
      (∀ T, IsSylowTwoOf T G →
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
          (π : ↥(StatedSp 2 F) →* ↥L) (W : Submodule F ((Fin 2 ⊕ Fin 2) → F))
          (X : Subgroup (MulAut V)),
          Nat.card F = 2 ^ (2 * s) ∧
          (FFModel.twistTensor s (StatedSp 2 F)).RealizesVia L ⊤ ⊥ π ∧
          TrivialOnDynkinVia G L (StatedSp 2 F) π ∧ IsSp4IsotropicPlane W ∧
          X = markedPlaneImage L (StatedSp 2 F) π W ∧
          IsA2 T X ∧ rk ↥X = 6 * s ∧ rk ↥(fixV X) = 4 * s ∧
          rAV X = 2 ∧ commSeries X 3 = ⊥ ∧
          ∀ A, IsA2 T A → rAV A ≤ 2 → A = X) ∧
      AsB45Part3 G L

section BurnsideK3


section Ctx

open CFSG.Quasithin CFSG.Quasithin.B45Sp4 CFSG.Quasithin.B42Sp4 CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor

@[expose] def burnsideK3_pi {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {K : Type} [Field K]
    [CharP K 2] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] (θ : V ≃* Multiplicative W)
    (θL : ↥L ≃* ↥(antiSp K)) : ↥(antiSp K) →* (W ≃ₗ[ZMod 2] W) :=
  (binPsi θ).toMonoidHom.comp (L.subtype.comp θL.symm.toMonoidHom)


structure burnsideK3_Ctx (V : Type) [CommGroup V] (L : Subgroup (MulAut V)) (a : ℕ) where
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  [instChar : CharP K 2]
  W : Type
  [instAC : AddCommGroup W]
  [instMod : Module (ZMod 2) W]
  [instFW : Finite W]
  hK : Nat.card K = 2 ^ (2 * a)
  θ : V ≃* Multiplicative W
  θL : ↥L ≃* ↥(antiSp K)
  [irr : Fact (repOf (burnsideK3_pi θ θL)).IsIrreducible]
  hD : Nat.card (EndRing (repOf (burnsideK3_pi θ θL))) = 2 ^ a
  hdim : Module.finrank (EndRing (repOf (burnsideK3_pi θ θL))) W = 16
  j : ℕ
  φ : W ≃+ ↥(hermA a (Fin 2 ⊕ Fin 2) K)
  hφ : ∀ (g : ↥(antiSp K)) (w : W),
    (φ (burnsideK3_pi θ θL g w) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      tw a (spMat (antiSpEquiv K ((minorAut K ^ j) g))) (φ w)

attribute [instance] burnsideK3_Ctx.instField burnsideK3_Ctx.instFinite burnsideK3_Ctx.instChar
  burnsideK3_Ctx.instAC burnsideK3_Ctx.instMod burnsideK3_Ctx.instFW burnsideK3_Ctx.irr


open CFSG.Quasithin.B45Sp4 in
@[expose] noncomputable def burnsideK3_twAdd {K : Type} [Field K] [CharP K 2] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a)) (y : ↥(StatedSp 2 K)) :
    ↥(hermA a (Fin 2 ⊕ Fin 2) K) ≃+ ↥(hermA a (Fin 2 ⊕ Fin 2) K) where
  toFun Y := ⟨tw a (spMat y) (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
    tw_mem_hermA hK _ Y.2⟩
  invFun Y := ⟨tw a (spMat y⁻¹) (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
    tw_mem_hermA hK _ Y.2⟩
  left_inv Y := by
    apply Subtype.ext
    show tw a (spM y⁻¹) (tw a (spM y) _) = _
    rw [← tw_mul, ← spM_mul, inv_mul_cancel, spM_one, tw_one]
  right_inv Y := by
    apply Subtype.ext
    show tw a (spM y) (tw a (spM y⁻¹) _) = _
    rw [← tw_mul, ← spM_mul, mul_inv_cancel, spM_one, tw_one]
  map_add' Y Z := by
    apply Subtype.ext
    exact tw_add a _ _ _


structure burnsideK3_Coord (V : Type) [CommGroup V] (L : Subgroup (MulAut V)) (a : ℕ) where
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  [instChar : CharP K 2]
  W : Type
  [instAC : AddCommGroup W]
  [instMod : Module (ZMod 2) W]
  hK : Nat.card K = 2 ^ (2 * a)
  θ : V ≃* Multiplicative W
  δ : ↥L ≃* ↥(StatedSp 2 K)
  φ : W ≃+ ↥(hermA a (Fin 2 ⊕ Fin 2) K)
  hφL : ∀ (l : ↥L) (w : W),
    (φ (binPsi θ (l : MulAut V) w) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      tw a (spMat (δ l)) (φ w)

attribute [instance] burnsideK3_Coord.instField burnsideK3_Coord.instFinite
  burnsideK3_Coord.instChar burnsideK3_Coord.instAC burnsideK3_Coord.instMod


@[reducible, expose] noncomputable def burnsideK3_Coord.conj {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {a : ℕ} (c : burnsideK3_Coord V L a) (y : ↥(StatedSp 2 c.K)) : burnsideK3_Coord V L a where
  K := c.K
  W := c.W
  hK := c.hK
  θ := c.θ
  δ := c.δ.trans (MulAut.conj y)
  φ := c.φ.trans (burnsideK3_twAdd c.hK y)
  hφL := fun l w => by
    show (tw a (spMat y) ((c.φ (binPsi c.θ (l : MulAut V) w) :
      ↥(hermA a (Fin 2 ⊕ Fin 2) c.K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) c.K)) =
      tw a (spMat (y * c.δ l * y⁻¹)) (tw a (spMat y) ((c.φ w : ↥(hermA a (Fin 2 ⊕ Fin 2) c.K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) c.K))
    rw [c.hφL, ← tw_mul, ← tw_mul]
    show tw a (spM y * spM (c.δ l)) _ = tw a (spM (y * c.δ l * y⁻¹) * spM y) _
    rw [← spM_mul, ← spM_mul, mul_assoc, inv_mul_cancel, mul_one]


section Sym

open Matrix

variable {F : Type} [Field F] [CharP F 2] {ι : Type} [Fintype ι] [DecidableEq ι]


end Sym

section FixF

open CFSG.Quasithin.B45Sp4


end FixF


section Inn

open CFSG.Quasithin CFSG.Quasithin.B42Sp4 CFSG.Quasithin.B45Sp4 CFSG.Quasithin.H.Sp4 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (sym2 sym2_transpose tau coe_tau lam coe_lam radical mem_unipotent_iff eq_sym2 tau_mul_tau tau_comm tau_injective card_radical unitri tau_sq)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open scoped Matrix

variable {K : Type} [Field K]


end Inn

section Out

open CFSG.Quasithin CFSG.Quasithin.B45Sp4 CFSG.Quasithin.B42Sp4 CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
open scoped Matrix

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {a : ℕ}


end Out


end Ctx

end BurnsideK3

section


end


section


end

@[expose] def K_3_5 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    ∀ r : ℕ, IsG2Derived r (Lbar L) → G2NaturalDerived L ⊤ ⊥ r →
      ((r = 1 ∧ G = L) → qOf G = qc (3 / 2) ∧ qhatOf G = qc (3 / 2)) ∧
      (¬ (r = 1 ∧ G = L) → ∀ A, IsFFStarOffender G A → B42Case4 G L A)

section


end

@[expose] def K_3_6 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), KSetup V G L →
    ∀ r : ℕ, IsSz r (Lbar L) → BinaryNaturalSz L ⊤ ⊥ r →
      Odd (MonoidHom.range (MulAut.conj : ↥L →* MulAut ↥L)).index ∧
      L = oTwoPrimeRes G ∧
      ∀ T, IsSylowTwoOf T G →
        rk ↥(ChIJK.omegaOne T) = r ∧
        (∀ x ∈ ChIJK.omegaOne T, x ≠ 1 → commV (Subgroup.zpowers x) = fixV (Subgroup.zpowers x)) ∧
        rk ↥(fixV (ChIJK.omegaOne T)) = 2 * r ∧ rAV (ChIJK.omegaOne T) = 2 ∧
        IsQuadratic (ChIJK.omegaOne T) ∧
        qhatOf G = qc 2 ∧ qOf G = qc 2 ∧ Qset T = {ChIJK.omegaOne T}

section


end

end CFSG.ASVolI
