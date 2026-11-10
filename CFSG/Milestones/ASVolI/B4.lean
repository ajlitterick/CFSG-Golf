module

public import CFSG.Milestones.ASVolI.B2
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.B4L3Three
public import CFSG.Open.QuasithinH1NaturalModulesMilestoneDefs
public import CFSG.Quasithin.Background.F918E1
public import CFSG.Quasithin.Background.B412Two
public import CFSG.Quasithin.Background.A7Q528Main
public import CFSG.Quasithin.Background.JonesParshallSLn
public import CFSG.Quasithin.Vol2.Ch10SecV1H
public import CFSG.Quasithin.Background.B4L3Two

public section

namespace CFSG.ASVolI.ChB

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

section DualGen

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]

@[expose] def fixedSubF (A : Subgroup (M ≃ₗ[F] M)) : Submodule F M :=
  ⨅ a ∈ A, LinearMap.ker ((a : M →ₗ[F] M) - LinearMap.id)

@[expose] def commSubF (A : Subgroup (M ≃ₗ[F] M)) : Submodule F M :=
  ⨆ a ∈ A, LinearMap.range ((a : M →ₗ[F] M) - LinearMap.id)

@[expose] def IsQuadraticF (A : Subgroup (M ≃ₗ[F] M)) : Prop :=
  commSubF A ≤ fixedSubF A

@[expose] def dualRep : (M ≃ₗ[F] M) →* (Module.Dual F M ≃ₗ[F] Module.Dual F M) where
  toFun g := g.symm.dualMap
  map_one' := by
    ext f x
    rfl
  map_mul' g h := by
    ext f x
    rfl

end DualGen

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI.ChB

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

section ChiefSeries

variable {V : Type*} [CommGroup V]

@[expose] def HasOneNatChief (G : Subgroup (MulAut V)) (d a : ℕ) : Prop :=
  ∃ (m : ℕ) (S : ℕ → Subgroup V), (∀ i, i ≤ m → ∀ g ∈ G, ∀ x ∈ S i, g x ∈ S i) ∧
    S 0 = ⊥ ∧ S m = ⊤ ∧
    (∀ i, i < m → S i < S (i + 1) ∧ ∀ Z : Subgroup V, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) →
      S i ≤ Z → Z ≤ S (i + 1) → Z = S i ∨ Z = S (i + 1)) ∧
    ∃ j, j < m ∧ (∀ i, i < m → i ≠ j → ∀ g ∈ G, ∀ x ∈ S (i + 1), (g : MulAut V) x * x⁻¹ ∈ S i) ∧
      BinaryNaturalSL G (S (j + 1)) (S j) d a

end ChiefSeries

@[expose] noncomputable def h1CardOfRep {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι]
    [Field K] [Algebra (ZMod 2) K] (φ : G →* Matrix ι ι K) : ℕ :=
  Nat.card (groupCohomology (Rep.of (quasithinH1MatrixRep φ)) 1)

@[expose] noncomputable def orthModel6 : FFModel := FFModel.extSq (ZMod 2) 4

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI.ChB

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped TensorProduct

section B46

variable {K : Type} [Field K]

abbrev NatQ (K : Type) : Type := (Fin 3 → K) × (Fin 3 → K)

abbrev WeylM (K : Type) : Type := K × (Fin 3 → K) × (Fin 3 → K)

@[expose] def qAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (x : NatQ K) : NatQ K :=
  ((γ (0, x.1, x.2, 0)).2.1, (γ (0, x.1, x.2, 0)).2.2.1)

@[expose] def weylAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (x : WeylM K) : WeylM K :=
  ((γ (x.1, x.2.1, x.2.2, x.1)).1, (γ (x.1, x.2.1, x.2.2, x.1)).2.1,
    (γ (x.1, x.2.1, x.2.2, x.1)).2.2.1)

@[expose] def longRootFn (i j : Fin 3) (c : K) (x : quasithinZorn K) : quasithinZorn K :=
  (x.1, x.2.1 + Pi.single i (c * x.2.1 j), x.2.2.1 + Pi.single j (c * x.2.2.1 i), x.2.2.2)

@[expose] def shortRootFn (t : K) (x : quasithinZorn K) : quasithinZorn K :=
  (x.1 + t * x.2.2.1 0, x.2.1 + Pi.single 0 (t * (x.1 + x.2.2.2) + t ^ 2 * x.2.2.1 0),
    x.2.2.1 + Pi.single 2 (t * x.2.1 1) + Pi.single 1 (t * x.2.1 2), x.2.2.2 + t * x.2.2.1 0)

@[expose] def IsRootConj {V : Type} [CommGroup V] (π : ↥(quasithinG2 K) →* MulAut V)
    (f : K → quasithinZorn K → quasithinZorn K) (Z : Subgroup (MulAut V)) : Prop :=
  ∃ g : ↥(quasithinG2 K), ∀ ψ : MulAut V, ψ ∈ Z ↔
    ∃ (c : K) (φ : ↥(quasithinG2 K)),
      (∀ x, (φ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x = f c x) ∧ ψ = π g * π φ * (π g)⁻¹

@[expose] def IsLongRootSub {V : Type} [CommGroup V] (π : ↥(quasithinG2 K) →* MulAut V)
    (Z : Subgroup (MulAut V)) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ IsRootConj π (longRootFn i j) Z

@[expose] def IsShortRootSub {V : Type} [CommGroup V] (π : ↥(quasithinG2 K) →* MulAut V)
    (Z : Subgroup (MulAut V)) : Prop :=
  IsRootConj π shortRootFn Z

@[expose] def IsFPre {V : Type} [CommGroup V] (θ : V →* Multiplicative (NatQ K)) (d : ℕ)
    (X : Subgroup V) : Prop :=
  ∃ S : Submodule K (NatQ K), Module.finrank K S = d ∧
    ∀ v : V, v ∈ X ↔ Multiplicative.toAdd (θ v) ∈ S

variable {V : Type} [CommGroup V]

@[expose] def cPre (C : Subgroup V) (Z : Subgroup (MulAut V)) : Subgroup V :=
  ⨅ z ∈ Z, C.comap ((z : MulAut V).toMonoidHom * (MonoidHom.id V)⁻¹)

end B46

section B46Groups

variable {M : Type*} [Group M]

@[expose] def IsNatGL2Quot (K : Type) [Field K] (P R Y A : Subgroup M) : Prop :=
  R ≤ P ∧ A ≤ Y ∧
    P ≤ Subgroup.normalizer (Y : Set M) ∧ P ≤ Subgroup.normalizer (A : Set M) ∧
  ∃ (_ : (R.subgroupOf P).Normal) (θ' : ↥P ⧸ R.subgroupOf P ≃* GL (Fin 2) K)
      (ζ : ↥Y →* Multiplicative (Fin 2 → K)),
    Function.Surjective ζ ∧ ζ.ker = A.subgroupOf Y ∧
      ∀ (p : ↥P) (y y' : ↥Y), (y' : M) = (p : M) * (y : M) * (p : M)⁻¹ →
        ζ y' = Multiplicative.ofAdd
          (((θ' (QuotientGroup.mk p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
            (Multiplicative.toAdd (ζ y)))

@[expose] def IsNatGL2QuotTw (K : Type) [Field K] (P R Y A : Subgroup M) : Prop :=
  R ≤ P ∧ A ≤ Y ∧
    P ≤ Subgroup.normalizer (Y : Set M) ∧ P ≤ Subgroup.normalizer (A : Set M) ∧
  ∃ (_ : (R.subgroupOf P).Normal) (θ' : ↥P ⧸ R.subgroupOf P ≃* GL (Fin 2) K)
      (ζ : ↥Y →* Multiplicative (Fin 2 → K)),
    Function.Surjective ζ ∧ ζ.ker = A.subgroupOf Y ∧
      ∀ (p : ↥P) (y y' : ↥Y), (y' : M) = (p : M) * (y : M) * (p : M)⁻¹ →
        ζ y' = Multiplicative.ofAdd
          ((((θ' (QuotientGroup.mk p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) •
            (((θ' (QuotientGroup.mk p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
              (Multiplicative.toAdd (ζ y))))

@[expose] def IsSpecial2 (R Z : Subgroup M) : Prop :=
  IsPGroup 2 R ∧ centerOf R = Z ∧ ⁅R, R⁆ = Z ∧ (frattini ↥R).map R.subtype = Z ∧ Z ≠ ⊥

@[expose] def IsStrongClosedWrt (Z R G : Subgroup M) : Prop :=
  ∀ x ∈ Z, ∀ g ∈ G, g * x * g⁻¹ ∈ R → g * x * g⁻¹ ∈ Z

end B46Groups

section B46Module

variable {V : Type} [CommGroup V]

@[expose] def IsNatGL2SecMod (K : Type) [Field K] (P R : Subgroup (MulAut V)) (Y C : Subgroup V) :
    Prop :=
  R ≤ P ∧ C ≤ Y ∧
    (∀ p ∈ P, ∀ y ∈ Y, (p : MulAut V) y ∈ Y) ∧
    (∀ p ∈ P, ∀ c ∈ C, (p : MulAut V) c ∈ C) ∧
  ∃ (_ : (R.subgroupOf P).Normal) (θ' : ↥P ⧸ R.subgroupOf P ≃* GL (Fin 2) K)
      (ζ : ↥Y →* Multiplicative (Fin 2 → K)),
    Function.Surjective ζ ∧ ζ.ker = C.subgroupOf Y ∧
      ∀ (p : ↥P) (y y' : ↥Y), (y' : V) = (p : MulAut V) (y : V) →
        ζ y' = Multiplicative.ofAdd
          (((θ' (QuotientGroup.mk p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
            (Multiplicative.toAdd (ζ y)))

section B46Cfg

variable {V : Type} [CommGroup V] {K : Type} [Field K]

@[expose] def B46Cfg1 (G L : Subgroup (MulAut V)) (θ : V →* Multiplicative (NatQ K))
    (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
    (A₁ : Subgroup (MulAut V)) : Prop :=
  IsFPre θ 1 V₁ ∧ P₁ = L ⊓ stabSub V₁ ∧ R₁ = pCoreOf 2 P₁ ∧ Z₁ = centerOf R₁ ∧
    V₃ = cPre (fixV L) Z₁ ∧ ∀ g : MulAut V, g ∈ A₁ ↔ g ∈ G ∧ ∀ v ∈ V₃, g v * v⁻¹ ∈ fixV L

@[expose] def B46Cfg2 (G L P₁ : Subgroup (MulAut V)) (T Z₂ P₂ R₂ : Subgroup (MulAut V))
    (V₂ : Subgroup V) : Prop :=
  IsSylowTwoOf T G ∧ T ⊓ L ≤ P₁ ∧ Z₂ = centerOf (T ⊓ L) ∧
    P₂ = L ⊓ Subgroup.normalizer (Z₂ : Set (MulAut V)) ∧ R₂ = pCoreOf 2 P₂ ∧
    V₂ = cPre (fixV L) R₂

end B46Cfg

end B46Module

section B49

variable {V : Type} [CommGroup V]

@[expose] def QuotIsoSub (G : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∃ φ : V ⧸ U ≃* ↥U, ∀ g ∈ G, ∀ v : V,
    ((φ (QuotientGroup.mk ((g : MulAut V) v)) : ↥U) : V) =
      (g : MulAut V) ((φ (QuotientGroup.mk v) : ↥U) : V)

@[expose] def QuotIsoDual (G : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∃ φ : V ⧸ U ≃* DualGrp ↥U, ∀ g ∈ G, ∀ v : V, ∀ u u' : ↥U,
    (g : MulAut V) (u' : V) = (u : V) →
      (φ (QuotientGroup.mk ((g : MulAut V) v))) u = (φ (QuotientGroup.mk v)) u'

@[expose] def SplitsOver (G : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∃ U' : Subgroup V, (∀ g ∈ G, ∀ u ∈ U', (g : MulAut V) u ∈ U') ∧ U ⊓ U' = ⊥ ∧ U ⊔ U' = ⊤

@[expose] def IsTransvOnQuot (U : Subgroup V) (f : ℕ) (e : MulAut V) : Prop :=
  Nat.card ↥(commV (Subgroup.zpowers e) ⊔ U) = Nat.card ↥U * 2 ^ f

@[expose] def axisPre (U : Subgroup V) (e : MulAut V) : Set V := {v | e v * v⁻¹ ∈ U}

@[expose] def IsTransvFourGrpFixedAxis (G : Subgroup (MulAut V)) (U : Subgroup V) (f : ℕ)
    (E : Subgroup (MulAut V)) : Prop :=
  E ≤ G ∧ Nat.card E = 4 ∧ (∀ e ∈ E, e ≠ 1 → IsTransvOnQuot U f e) ∧
    ∃ H : Set V, ∀ e ∈ E, e ≠ 1 → axisPre U e = H

@[expose] def InRootGroup {K : Type} [Field K] {n : ℕ} (G : Subgroup (MulAut V))
    (π : ↥(StatedSL n K) →* ↥G) (E : Subgroup (MulAut V)) : Prop :=
  ∃ (g : ↥G) (i j : Fin n), i ≠ j ∧ ∀ e ∈ E, ∃ (s : ↥(StatedSL n K)) (c : K),
    ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + Matrix.single i j c ∧
      ((π s : ↥G) : MulAut V) = (g : MulAut V)⁻¹ * e * (g : MulAut V)

@[expose] def IsSubspaceStab (G : Subgroup (MulAut V)) (U : Subgroup V) (i : ℕ)
    (P : Subgroup (MulAut V)) : Prop :=
  ∃ W : Subgroup V, W ≤ U ∧ Nat.card W = 2 ^ i ∧ P = G ⊓ stabSub W

@[expose] def IsLeviComplement (P M : Subgroup (MulAut V)) : Prop :=
  M ≤ P ∧ M ⊓ pCoreOf 2 P = ⊥ ∧ M ⊔ pCoreOf 2 P = P

end B49

section B414

variable (F : Type) [Field F]

abbrev PGL3 : Type := GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)

@[expose] noncomputable def sl3Sub : Submodule F (Matrix (Fin 3) (Fin 3) F) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 3) F F)

variable {F}

@[expose] def twAdjMat (k : ℕ) (g : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F :=
  ((g : Matrix (Fin 3) (Fin 3) F).det) ^ k •
    ((g : Matrix (Fin 3) (Fin 3) F) * M * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))


@[expose] def TwAdjointIntertwines {V : Type} [CommGroup V] (G : Subgroup (MulAut V))
    (α : ↥G →* PGL3 F) (k : ℕ) (β : V ≃* Multiplicative ↥(sl3Sub F)) : Prop :=
  ∀ (element : ↥G) (vector : V) (representative : GL (Fin 3) F),
    (QuotientGroup.mk representative : PGL3 F) = α element →
      ((Multiplicative.toAdd (β ((element : MulAut V) vector)) : ↥(sl3Sub F)) :
        Matrix (Fin 3) (Fin 3) F) =
          twAdjMat k representative ((Multiplicative.toAdd (β vector) : ↥(sl3Sub F)) :
            Matrix (Fin 3) (Fin 3) F)

@[expose] def AdjointScalarCompatible {V M : Type} [CommGroup V] [AddCommGroup M] [Module F M]
    (β : V ≃* Multiplicative ↥(sl3Sub F)) (W : Subgroup V)
    (Φ : Multiplicative M ≃* ↥W) : Prop :=
  ∀ (scalar : F) (vector : M),
    β ((Φ (Multiplicative.ofAdd (scalar • vector)) : ↥W) : V) =
      Multiplicative.ofAdd (scalar • Multiplicative.toAdd
        (β ((Φ (Multiplicative.ofAdd vector) : ↥W) : V)))

@[expose] noncomputable def tensAct (A B : Matrix (Fin 2) (Fin 2) F) :
    (Fin 2 → F) ⊗[F] (Fin 2 → F) →ₗ[F] (Fin 2 → F) ⊗[F] (Fin 2 → F) :=
  TensorProduct.map (Matrix.toLin' A) (Matrix.toLin' B)

@[expose] noncomputable def tensActOf {K : Type} [Group K] (π₁ π₂ : K →* ↥(StatedSL 2 F)) (k : K) :
    (Fin 2 → F) ⊗[F] (Fin 2 → F) →ₗ[F] (Fin 2 → F) ⊗[F] (Fin 2 → F) :=
  tensAct (((π₁ k : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
    (((π₂ k : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)

@[expose] def TensorUniserialTrivEnds {K : Type} [Group K] (π₁ π₂ : K →* ↥(StatedSL 2 F)) : Prop :=
  let inv : Submodule F ((Fin 2 → F) ⊗[F] (Fin 2 → F)) → Prop :=
    fun A => ∀ k : K, ∀ m ∈ A, tensActOf π₁ π₂ k m ∈ A
  (∀ A B, inv A → inv B → A ≤ B ∨ B ≤ A) ∧
  (∃ A₀, inv A₀ ∧ A₀ ≠ ⊥ ∧ (∀ k : K, ∀ m ∈ A₀, tensActOf π₁ π₂ k m = m) ∧
    ∀ A, inv A → A ≠ ⊥ → A₀ ≤ A) ∧
  (∃ A₁, inv A₁ ∧ A₁ ≠ ⊤ ∧ (∀ k : K, ∀ m, tensActOf π₁ π₂ k m - m ∈ A₁) ∧
    ∀ A, inv A → A ≠ ⊤ → A ≤ A₁)

@[expose] def IsTensorOfNaturalsUniserialVia {V : Type} [CommGroup V]
    (β : V ≃* Multiplicative ↥(sl3Sub F)) (K : Subgroup (MulAut V)) (W : Subgroup V) : Prop :=
  ∃ π₁ π₂ : ↥K →* ↥(StatedSL 2 F), Function.Surjective π₁ ∧ Function.Surjective π₂ ∧
    ∃ Φ : Multiplicative ((Fin 2 → F) ⊗[F] (Fin 2 → F)) ≃* ↥W,
      (∀ (element : ↥K) (vector : (Fin 2 → F) ⊗[F] (Fin 2 → F)),
        ((Φ (Multiplicative.ofAdd (tensActOf π₁ π₂ element vector)) : ↥W) : V) =
          (element : MulAut V) ((Φ (Multiplicative.ofAdd vector) : ↥W) : V)) ∧
      AdjointScalarCompatible β W Φ ∧ TensorUniserialTrivEnds π₁ π₂

@[expose] def IsNaturalSL2ViaAdjoint {V : Type} [CommGroup V]
    (β : V ≃* Multiplicative ↥(sl3Sub F)) (K : Subgroup (MulAut V)) (W : Subgroup V) : Prop :=
  ∃ π : ↥K →* ↥(StatedSL 2 F), Function.Surjective π ∧
    ∃ Φ : Multiplicative (Fin 2 → F) ≃* ↥W,
      (∀ (element : ↥K) (vector : Fin 2 → F),
        ((Φ (natAct (StatedSL 2 F) (π element) (Multiplicative.ofAdd vector)) : ↥W) : V) =
          (element : MulAut V) ((Φ (Multiplicative.ofAdd vector) : ↥W) : V)) ∧
      AdjointScalarCompatible β W Φ

end B414

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

@[expose] def B_4_7 : Prop :=
  (∀ (F : Type) [Field F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (A : Subgroup (V ≃ₗ[F] V)), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
    (Function.Bijective (Submodule.dualAnnihilator : Submodule F V → Submodule F (Module.Dual F V)) ∧
      (∀ U U' : Submodule F V, U ≤ U' ↔ U'.dualAnnihilator ≤ U.dualAnnihilator) ∧
      (∀ (g : V ≃ₗ[F] V) (U : Submodule F V),
        (U.map (g : V →ₗ[F] V)).dualAnnihilator =
          U.dualAnnihilator.map ((dualRep g : Module.Dual F V ≃ₗ[F] Module.Dual F V) :
            Module.Dual F V →ₗ[F] Module.Dual F V)) ∧
      (∀ U : Submodule F V, Module.finrank F ↥(U.dualAnnihilator) + Module.finrank F ↥U =
        Module.finrank F V)) ∧
    ((commSubF A).dualAnnihilator =
        fixedSubF (M := Module.Dual F V) (A.map (dualRep (F := F) (M := V))) ∧
      (fixedSubF A).dualAnnihilator =
        commSubF (M := Module.Dual F V) (A.map (dualRep (F := F) (M := V)))) ∧
    (IsQuadraticF A ↔ IsQuadraticF (M := Module.Dual F V) (A.map (dualRep (F := F) (M := V))))) ∧
  (∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ A : Subgroup (MulAut V), IsElemAbelian2 A → A ≠ ⊥ → IsQuadratic A →
      rk (commV A) ≤ 2 * rk A → qOf (dualSub A) ≤ 2)

section BurnsideB4a


end BurnsideB4a


@[expose] def B_4_8 : Prop :=
  (∀ (G : Type) [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) (ZMod 2)), Function.Injective ρ →
    Nat.card G = 168 → h1CardOfRep ρ = 2) ∧
  (∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), Nat.card V = 16 → BinaryNaturalSL G ⊤ (fixV G) 3 1 →
      IsIndecompModule G →
        (∃ A : Subgroup (MulAut V), IsCenterTransvGroup G A ∧
            {B | IsFFStarOffender G B} = {B | ∃ g ∈ G, B = B1.conjAut g A}) ∧
        qOf G = 1 ∧
        (∀ T : Subgroup (MulAut V), IsSylowTwoOf T G → fixV T = fixV G) ∧
        (∀ a ∈ G, a ≠ 1 → a ^ 2 = 1 →
          commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
            rk (fixV (Subgroup.zpowers a)) = 2)) ∧
  (∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), Nat.card V = 16 → BinaryNaturalSL G (commV G) ⊥ 3 1 →
      IsIndecompModule G →
        (∃ B : Subgroup (MulAut V), IsAxisTransvGroup G B ∧
            {A | IsFFStarOffender G A} = {A | ∃ g ∈ G, A = B1.conjAut g B}) ∧
        qOf G = 1 ∧
        (∀ a ∈ G, a ≠ 1 → a ^ 2 = 1 →
          commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
            rk (fixV (Subgroup.zpowers a)) = 2 ∧ fixV (Subgroup.zpowers a) ≤ commV G)) ∧
  (∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), Nonempty (↥G ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      IsIndecompModule G → HasOneNatChief G 3 1 →
        Nat.card V = 2 ^ 3 ∨ Nat.card V = 2 ^ 4)

section BurnsideB4b


attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent in

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent in


end BurnsideB4b

section


end

@[expose] def B_4_10 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut V)) (u : V), u ≠ 1 → (∀ t : MulAut V, IsTransvectionWith t u → t ∈ G) →
      ∀ (U : Subgroup V) (L : Subgroup (MulAut V)),
        U = Subgroup.closure {y | ∃ g ∈ G, g u = y} →
        L = Subgroup.closure {x | ∃ g ∈ G, ∃ t : MulAut V, IsTransvectionWith t u ∧ x = g * t * g⁻¹} →
          autSub L U = ⊤


@[expose] def B_4_11 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), Nonempty (↥G ≃* alternatingGroup (Fin 7)) →
      Nontrivial V → (∀ W : Subgroup V, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) →
        Nat.card V ≤ 2 ^ 8 → Nat.card V = 2 ^ 4 ∨ Nat.card V = 2 ^ 6


@[expose] def B_4_12 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut V)) (v : V), Subgroup.closure (orbitOf G v) = ⊤ →
      (∃ U : Subgroup V, (∃ x ∈ U, ∃ y ∈ U, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y) ∧
        ∀ u ∈ U, u ≠ 1 → u ∈ orbitOf G v) →
        (IsTwoTransitiveOn G (orbitOf G v) → {x : V | x ≠ 1} = orbitOf G v) ∧
        ((Nonempty (↥G ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
            Nonempty (↥G ≃* alternatingGroup (Fin 7))) →
          Odd (Nat.card (orbitOf G v)) →
          Nonempty (↥(G ⊓ MulAction.stabilizer (MulAut V) v) ⧸
              CFSG.pCore 2 ↥(G ⊓ MulAction.stabilizer (MulAut V) v) ≃*
            Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
          Nat.card V = 2 ^ 4 ∧ {x : V | x ≠ 1} = orbitOf G v)


@[expose] def B_4_13 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut V)) (π : orthModel6.Gam ≃* ↥G) (v : V) (H T : Subgroup (MulAut V)),
      v ≠ 1 → Subgroup.closure (orbitOf G v) = ⊤ →
      IsParabolic2 G (G ⊓ MulAction.stabilizer (MulAut V) v) →
      (∃ x : orthModel6.Amb, x ≠ 1 ∧
        ∀ g : MulAut V, g ∈ G ⊓ MulAction.stabilizer (MulAut V) v ↔
          ∃ s : orthModel6.Gam, orthModel6.act s x = x ∧ ((π s : ↥G) : MulAut V) = g) →
      IsParabolic2 G H →
      (∃ (E : Subgroup ↥H) (_ : E.Normal), IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
        Nonempty (↥H ⧸ E ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) →
      IsSylowTwoOf T G → T ≤ G ⊓ MulAction.stabilizer (MulAut V) v → T ≤ H →
      rk ↥(Subgroup.closure (orbitOf H v)) = 3 →
        ∃ β : V ≃* orthModel6.Amb, ∀ (s : orthModel6.Gam) (u : V),
          β (((π s : ↥G) : MulAut V) u) = orthModel6.act s (β u)

@[expose] def B_4_14 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = 4 →
    ∀ (G : Subgroup (MulAut V)) (α : ↥G ≃* PGL3 F),
      Nontrivial V → (∀ W : Subgroup V, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) →
      ∀ P : Subgroup (MulAut V), IsMaxParabolic2 G P →
      ∀ X : Subgroup (MulAut V), X ≤ P → Nat.card X = 3 →
      (∀ x ∈ X, ∀ l ∈ perfectCore P, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 (perfectCore P)) →
      (∀ C₁ C₂ : Subgroup V, C₁ < C₂ →
        (∀ l ∈ perfectCore P, ∀ c ∈ C₁, l c ∈ C₁) → (∀ l ∈ perfectCore P, ∀ c ∈ C₂, l c ∈ C₂) →
        (∀ J : Subgroup V, (∀ l ∈ perfectCore P, ∀ c ∈ J, l c ∈ J) → C₁ ≤ J → J ≤ C₂ →
          J = C₁ ∨ J = C₂) →
        (∃ l ∈ perfectCore P, ∃ c ∈ C₂, l c * c⁻¹ ∉ C₁) →
          BinaryNaturalSL (ChB.autSec (perfectCore P) C₂ C₁) ⊤ ⊥ 2 2) →
        ∃ k : ℕ, k < 3 ∧ ∃ β : V ≃* Multiplicative ↥(sl3Sub F),
          TwAdjointIntertwines G α.toMonoidHom k β ∧
          (k = 0 → IsTensorOfNaturalsUniserialVia β
              (perfectCore P ⊓ Subgroup.centralizer (X : Set (MulAut V))) (fixV X)) ∧
          (k ≠ 0 → IsNaturalSL2ViaAdjoint β
              (perfectCore P ⊓ Subgroup.centralizer (X : Set (MulAut V))) (fixV X)) ∧
          (∀ (otherTwist : ℕ), otherTwist < 3 →
            ∀ otherIdentification : V ≃* Multiplicative ↥(sl3Sub F),
              TwAdjointIntertwines G α.toMonoidHom otherTwist otherIdentification →
                otherTwist = k)

@[expose] def B_4_9 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (n f : ℕ), ((4 ≤ n ∧ f = 1) ∨ (n = 3 ∧ 1 ≤ f)) →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
    ∀ (G : Subgroup (MulAut V)) (U : Subgroup V) (π : ↥(StatedSL n K) →* ↥G),
      (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π →
      (QuotIsoSub G U ∨ QuotIsoDual G U) →
      (∀ E : Subgroup (MulAut V), IsTransvFourGrpFixedAxis G U f E → IsQuadratic E →
        (n = 3 → ¬ InRootGroup G π E) →
        (n = 3 → f = 2 → ∀ E' : Subgroup (MulAut V), IsTransvFourGrpFixedAxis G U f E' →
          ¬ InRootGroup G π E' → IsQuadratic E') →
          SplitsOver G U) ∧
      (∀ T : Subgroup (MulAut V), IsSylowTwoOf T G → ∀ A : Subgroup (MulAut V), IsFFStarOffender T A →
        SplitsOver G U ∧
        (n = 3 → QuotIsoSub G U ∧ qOf G = ((1 : ℚ) : WithTop ℚ)) ∧
        (n = 4 → QuotIsoDual G U → A = Jj T 0 ∧ rk ↥A = 4 ∧ qOf G = ((1 : ℚ) : WithTop ℚ)) ∧
        (n = 5 → QuotIsoDual G U → qOf G = ((5 / 6 : ℚ) : WithTop ℚ) ∧
          ((IsElemAbelian 2 A ∧ Nat.card A = 16 ∧ ∃ P M : Subgroup (MulAut V),
              (IsSubspaceStab G U 1 P ∨ IsSubspaceStab G U 4 P) ∧ IsLeviComplement P M ∧ A ≤ M) ∨
            (IsElemAbelian 2 A ∧ (Nat.card A = 32 ∨ Nat.card A = 64) ∧ ∃ P : Subgroup (MulAut V),
              (IsSubspaceStab G U 2 P ∨ IsSubspaceStab G U 3 P) ∧ A ≤ pCoreOf 2 P))))

@[expose] def B_4_6 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (n : ℕ), 1 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n →
  ∀ (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
    (θ : V →* Multiplicative (NatQ K)),
    Function.Injective π → π.range = L → L ≤ G →
    quasithinGenFitting G = layerOf L → commV (layerOf L) = ⊤ →
    Function.Surjective θ → θ.ker = fixV L →
    (∀ (γ : ↥(quasithinG2 K)) (v : V), θ ((π γ) v) = Multiplicative.ofAdd
      (qAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (θ v)))) →
    ((∀ ψ : Multiplicative (NatQ K) →* Multiplicative (NatQ K),
        (∀ l ∈ L, ∀ v w : V, ψ (θ v) = θ w → ψ (θ (l v)) = θ (l w)) →
          ∃ c : K, ∀ x, ψ x = Multiplicative.ofAdd (c • Multiplicative.toAdd x)) ∧
      (∀ (c : K), ∀ l ∈ L, ∀ v w : V,
        θ w = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ v)) →
          θ (l w) = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ (l v)))) ∧
      Nat.card V ≤ 2 ^ (7 * n) ∧
      (Nat.card V = 2 ^ (7 * n) → ∃ Ψ : V ≃* Multiplicative (WeylM K),
        ∀ (γ : ↥(quasithinG2 K)) (v : V), Ψ ((π γ) v) = Multiplicative.ofAdd
          (weylAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (Ψ v))))) ∧
    (∀ v w : V, θ v ≠ 1 → θ w ≠ 1 → ∃ l ∈ L, θ (l v) = θ w) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
        IsMaxParabolic2 L P₁ ∧ Nat.card R₁ = Nat.card K ^ 5 ∧ IsNatGL2QuotTw K P₁ R₁ Z₁ ⊥ ∧
        IsFPre θ 3 V₃ ∧ (IsElemAbelian 2 A₁ ∧ Nat.card A₁ = Nat.card K ^ 3) ∧
        IsNatGL2Quot K P₁ R₁ R₁ A₁ ∧
        ∀ E : Subgroup V,
          E = ⨆ (Z : Subgroup (MulAut V)) (_ : IsLongRootSub π Z ∧ Z ≤ Z₁), cPre (fixV L) Z →
            IsFPre θ 5 E ∧ commSub E A₁ ⊔ fixV L = V₃) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        (IsElemAbelian 2 Z₂ ∧ Nat.card Z₂ = Nat.card K ∧ IsLongRootSub π Z₂) ∧
        (IsMaxParabolic2 L P₂ ∧ T ⊓ L ≤ P₂ ∧ P₂ ≠ P₁) ∧
        (IsSpecial2 R₂ Z₂ ∧ Nat.card R₂ = Nat.card K ^ 5) ∧
        IsNatGL2SecMod K P₂ R₂ V₂ (fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → V₂ = commV (Subgroup.zpowers z) ⊔ fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → cPre (fixV L) Z₂ = cPre (fixV L) (Subgroup.zpowers z) ∧
          IsFPre θ 4 (cPre (fixV L) Z₂))) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsLongRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
          ∃ l ∈ L, x = l * z * l⁻¹) ∧
        (∃ r : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ r ∈ Z ∧ r ≠ 1) ∧
          (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
            ∃ l ∈ L, x = l * r * l⁻¹) ∧
          ¬ (∃ l ∈ L, r = l * z * l⁻¹) ∧
          ∀ x ∈ L, x ≠ 1 → x ^ 2 = 1 → (∃ l ∈ L, x = l * z * l⁻¹) ∨ (∃ l ∈ L, x = l * r * l⁻¹)) ∧
        (L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) =
            L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) ∧
          L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) = twoPrimeResidual P₂)) ∧
    (∀ R : Subgroup (MulAut V), IsShortRootSub π R → ∀ r ∈ R, r ≠ 1 →
      L ⊓ Subgroup.centralizer ({r} : Set (MulAut V)) = L ⊓ Subgroup.centralizer (R : Set (MulAut V)) ∧
      ∃ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ ∧ IsIntDirProd A₁ ![Z₁, R] ∧
        (cPre (fixV L) (Subgroup.zpowers r) = V₃ ∧ cPre (fixV L) R = V₃ ∧
          commV (Subgroup.zpowers r) ⊔ fixV L = V₃) ∧
        ∃ L₁ : Subgroup (MulAut V), IsLeviComplement P₁ L₁ ∧
          L ⊓ Subgroup.normalizer (R : Set (MulAut V)) = A₁ ⊔ L₁) ∧
    (∀ i ∈ L, i ≠ 1 → i ^ 2 = 1 →
      cPre (fixV L) (Subgroup.zpowers i) = fixV (Subgroup.zpowers i) ⊔ fixV L) ∧
    (1 < n → ∀ R : Subgroup (MulAut V), IsShortRootSub π R → fixV L ≤ commV R) ∧
    (E3.aParam G = 2 * n ∧ (∀ A ∈ E3.aSet 2 G, A ≤ L) ∧
      ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
          E3.aSet (2 * n) G = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
          ∀ A ∈ E3.aSet (n + 1) G, ∃ l ∈ L, A.map (MulAut.conj l).toMonoidHom ≤ A₁) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        Set.ncard {X : Subgroup V | ∃ p ∈ P₁, X = V₂.map (p : MulAut V).toMonoidHom} = Nat.card K + 1 ∧
        (∀ p ∈ P₁, V₁ ≤ V₂.map (p : MulAut V).toMonoidHom ∧ V₂.map (p : MulAut V).toMonoidHom ≤ V₃) ∧
        (∀ p ∈ P₁, ∀ p' ∈ P₁, V₂.map (p : MulAut V).toMonoidHom ≠ V₂.map (p' : MulAut V).toMonoidHom →
          V₂.map (p : MulAut V).toMonoidHom ⊓ V₂.map (p' : MulAut V).toMonoidHom = V₁) ∧
        (∀ v ∈ V₃, ∃ p ∈ P₁, v ∈ V₂.map (p : MulAut V).toMonoidHom)) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ B : Subgroup (MulAut V), B ≤ G → (∀ b ∈ B, b ≠ 1 → ∃ l ∈ L, b = l * z * l⁻¹) →
          ∃ l ∈ L, B.map (MulAut.conj l).toMonoidHom ≤ Z₁) ∧
        IsStrongClosedWrt Z₁ R₁ G) ∧
    (1 < n → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ → ∀ A ∈ E3.aSet (2 * n - 1) G, A ≤ R₁ → A ≤ A₁) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        {A | IsFFStarOffender G A} = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
        ffJ T = R₂ ∧ ffJ R₁ = A₁) ∧
    (n = 2 → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ X : Subgroup (MulAut V), X ≤ G → Nat.card X = 3 → (X : Set (MulAut V)) * (T : Set (MulAut V)) =
          (T : Set (MulAut V)) * (X : Set (MulAut V)) →
        (X ≤ P₁ ⊓ perfectCore P₂ ↔ ⁅X, perfectCore P₁⁆ ≤ R₁))

end CFSG.ASVolI
