module

public import CFSG.Milestones.ASVolI.F3
public import CFSG.Milestones.ASVolI.F1
public import CFSG.Quasithin.Recognition.F4Small
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverChevalley
public import CFSG.LieType.Ree.ReeGenericPerfect
public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis

public noncomputable section

local instance : NeZero CFSG.Blueprint.Chevalley.Tag.D4.rank := ⟨by decide⟩
local instance : NeZero CFSG.Blueprint.Chevalley.Tag.F4.rank := ⟨by decide⟩

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.Blueprint CFSG.Blueprint.Chevalley

inductive GLKind
  | L3 | Sp4 | G2 | D4tw | F4tw | U4 | U5 | G2d | Tits
  deriving DecidableEq

namespace GLKind

@[expose] def m : GLKind → ℕ
  | L3 => 3
  | Sp4 => 4
  | G2 => 6
  | D4tw => 6
  | F4tw => 8
  | U4 => 4
  | U5 => 4
  | G2d => 6
  | Tits => 8


end GLKind

@[expose] def IsTwoF4Two (H : Type) [Group H] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
    Nonempty (H ≃* (↥(reeFixedGroup Tag.F4 K reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1))) ⧸
      Subgroup.center ↥(reeFixedGroup Tag.F4 K reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1)))))

@[expose] def IsGenLie (H : Type) [Group H] : GLKind → ℕ → ℕ → Prop
  | .L3, p, f => p.Prime ∧ 1 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = p ^ f ∧ Nonempty (H ≃* StatedProj (StatedSL 3 K))
  | .Sp4, p, f => p.Prime ∧ 1 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = p ^ f ∧ Nonempty (H ≃* StatedProj (StatedSp 2 K))
  | .G2, p, f => p.Prime ∧ 1 ≤ f ∧ UntwistedChevalleyModel H Tag.G2 (p ^ f)
  | .D4tw, p, f => p.Prime ∧ 1 ≤ f ∧ TwistedChevalleyModel H TwistTag.D4 (p ^ f)
  | .F4tw, p, f => p = 2 ∧ Odd f ∧ ((f = 1 ∧ IsTwoF4Two H) ∨ (3 ≤ f ∧ ReeTitsModel H .twistedF4 p f))
  | .U4, p, f => p.Prime ∧ 1 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (p ^ f) ^ 2 ∧ Nonempty (H ≃* StatedProj (StatedSU 4 (p ^ f) K))
  | .U5, p, f => p.Prime ∧ 1 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (p ^ f) ^ 2 ∧ Nonempty (H ≃* StatedProj (StatedSU 5 (p ^ f) K))
  | .G2d, p, f => p = 2 ∧ f = 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (H ≃* CFSG.Blueprint.DerivedCentralQuotient (adjointGroup Tag.G2 K))
  | .Tits, p, f => p = 2 ∧ f = 1 ∧ ReeTitsModel H .Tits p f

@[expose] def IsSylowOf {E : Type} [Group E] (p : ℕ) (S H : Subgroup E) : Prop :=
  S ≤ H ∧ IsPGroup p S ∧ ¬ p ∣ S.relIndex H

@[expose] def oPPrime {E : Type} [Group E] (p : ℕ) (P : Subgroup E) : Subgroup E :=
  Subgroup.closure {x : E | x ∈ P ∧ ∃ k : ℕ, orderOf x = p ^ k}

@[expose] def IsLieParabolics {E : Type} [Group E] (p : ℕ) (H B P₁ P₂ : Subgroup E) : Prop :=
  (∃ S : Subgroup E, IsSylowOf p S H ∧ B = H ⊓ Subgroup.normalizer (S : Set E)) ∧ P₁ ≠ P₂ ∧
    P₁ ⊓ P₂ = B ∧
    ∀ Q : Subgroup E, (B ≤ Q ∧ Q ≤ H ∧ Q ≠ H ∧ ∀ R : Subgroup E, Q < R → R ≤ H → R = H) ↔
      (Q = P₁ ∨ Q = P₂)

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI.ChF.ClassicalRoots

open CFSG.Open Matrix

inductive Kind
  | L3 | Sp4 | U4 | U5
  deriving DecidableEq

abbrev Coord : Kind → Type
  | .L3 => Fin 3
  | .Sp4 => Fin 2 ⊕ Fin 2
  | .U4 => Fin 4
  | .U5 => Fin 5

instance (kind : Kind) : Fintype (Coord kind) := by cases kind <;> infer_instance
instance (kind : Kind) : DecidableEq (Coord kind) := by cases kind <;> infer_instance

def nativeGroup (kind : Kind) (q : ℕ) (K : Type) [Field K] :
    Subgroup (GL (Coord kind) K) :=
  match kind with
  | .L3 => StatedSL 3 K
  | .Sp4 => StatedSp 2 K
  | .U4 => StatedSU 4 q K
  | .U5 => StatedSU 5 q K

def matrixUnit {index : Type} [DecidableEq index] {K : Type} [Zero K]
    (row column : index) (parameter : K) : Matrix index index K :=
  fun row' column' => if row' = row ∧ column' = column then parameter else 0

def coordinateSpace {index : Type} {K : Type} [Zero K]
    (support : Set index) : Set (index → K) :=
  {vector | ∀ position, position ∉ support → vector position = 0}

def flagOne : (kind : Kind) → Set (Coord kind)
  | .L3 => {0}
  | .Sp4 => {Sum.inl 0}
  | .U4 => {0}
  | .U5 => {0}

def flagTwo : (kind : Kind) → Set (Coord kind)
  | .L3 => {0, 1}
  | .Sp4 => {Sum.inl 0, Sum.inl 1}
  | .U4 => {0, 1}
  | .U5 => {0, 1}

def rawStabilizer {index : Type} [Fintype index] [DecidableEq index]
    {K : Type} [Field K] (space : Set (index → K)) : Subgroup (GL index K) :=
  Subgroup.closure {actor | ∀ vector,
    (actor : Matrix index index K).mulVec vector ∈ space ↔ vector ∈ space}

def nativeParabolic (kind : Kind) (q : ℕ) (K : Type) [Field K]
    (basis : GL (Coord kind) K) (second : Bool) : Subgroup (nativeGroup kind q K) :=
  (rawStabilizer ((fun vector => (basis : Matrix (Coord kind) (Coord kind) K).mulVec vector) ''
    coordinateSpace (if second then flagTwo kind else flagOne kind))).comap
    (nativeGroup kind q K).subtype

def nativeBorel (kind : Kind) (q : ℕ) (K : Type) [Field K]
    (basis : GL (Coord kind) K) :
    Subgroup (nativeGroup kind q K) :=
  nativeParabolic kind q K basis false ⊓ nativeParabolic kind q K basis true

def hermitianGram (dimension : ℕ) (K : Type) [Field K] :
    Matrix (Fin dimension) (Fin dimension) K :=
  fun row column => if row.val + column.val + 1 = dimension then 1 else 0

def BasisCompatible (kind : Kind) (q : ℕ) (K : Type) [Field K]
    (basis : GL (Coord kind) K) : Prop :=
  match kind with
  | .L3 => basis = 1
  | .Sp4 => basis = 1
  | .U4 => ((basis : Matrix (Fin 4) (Fin 4) K).map (fun entry => entry ^ q)).transpose *
      (basis : Matrix (Fin 4) (Fin 4) K) = hermitianGram 4 K
  | .U5 => ((basis : Matrix (Fin 5) (Fin 5) K).map (fun entry => entry ^ q)).transpose *
      (basis : Matrix (Fin 5) (Fin 5) K) = hermitianGram 5 K

inductive PositiveRoot
  | a12 | a23 | a13 | difference | sum | longOne | longTwo | shortOne | shortTwo
  deriving DecidableEq

def RootAllowed : Kind → PositiveRoot → Prop
  | .L3, root => root = .a12 ∨ root = .a23 ∨ root = .a13
  | .Sp4, root => root = .difference ∨ root = .sum ∨ root = .longOne ∨ root = .longTwo
  | .U4, root => root = .difference ∨ root = .sum ∨ root = .longOne ∨ root = .longTwo
  | .U5, root => root = .difference ∨ root = .sum ∨ root = .longOne ∨ root = .longTwo ∨
      root = .shortOne ∨ root = .shortTwo

def ParameterAllowed (kind : Kind) (q : ℕ) {K : Type} [Field K]
    (root : PositiveRoot) (parameter central : K) : Prop :=
  match kind, root with
  | .U4, .longOne | .U4, .longTwo | .U5, .longOne | .U5, .longTwo =>
      parameter + parameter ^ q = 0
  | .U5, .shortOne | .U5, .shortTwo =>
      central + central ^ q + parameter * parameter ^ q = 0
  | _, _ => True

def linearRoot {K : Type} [Field K] (root : PositiveRoot) (parameter : K) :
    Matrix (Fin 3) (Fin 3) K :=
  match root with
  | .a12 => 1 + matrixUnit 0 1 parameter
  | .a23 => 1 + matrixUnit 1 2 parameter
  | .a13 => 1 + matrixUnit 0 2 parameter
  | _ => 1

def symplecticRoot {K : Type} [Field K] (root : PositiveRoot) (parameter : K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  match root with
  | .difference => 1 + matrixUnit (.inl 0) (.inl 1) parameter -
      matrixUnit (.inr 1) (.inr 0) parameter
  | .sum => 1 + matrixUnit (.inl 0) (.inr 1) parameter +
      matrixUnit (.inl 1) (.inr 0) parameter
  | .longOne => 1 + matrixUnit (.inl 0) (.inr 0) parameter
  | .longTwo => 1 + matrixUnit (.inl 1) (.inr 1) parameter
  | _ => 1

def unitaryRootFour {K : Type} [Field K] (q : ℕ) (root : PositiveRoot)
    (parameter : K) : Matrix (Fin 4) (Fin 4) K :=
  match root with
  | .difference => 1 + matrixUnit 0 1 parameter - matrixUnit 2 3 (parameter ^ q)
  | .sum => 1 + matrixUnit 0 2 parameter - matrixUnit 1 3 (parameter ^ q)
  | .longOne => 1 + matrixUnit 0 3 parameter
  | .longTwo => 1 + matrixUnit 1 2 parameter
  | _ => 1

def unitaryRootFive {K : Type} [Field K] (q : ℕ) (root : PositiveRoot)
    (parameter central : K) : Matrix (Fin 5) (Fin 5) K :=
  match root with
  | .difference => 1 + matrixUnit 0 1 parameter - matrixUnit 3 4 (parameter ^ q)
  | .sum => 1 + matrixUnit 0 3 parameter - matrixUnit 1 4 (parameter ^ q)
  | .longOne => 1 + matrixUnit 0 4 parameter
  | .longTwo => 1 + matrixUnit 1 3 parameter
  | .shortOne => 1 + matrixUnit 0 2 parameter - matrixUnit 2 4 (parameter ^ q) +
      matrixUnit 0 4 central
  | .shortTwo => 1 + matrixUnit 1 2 parameter - matrixUnit 2 3 (parameter ^ q) +
      matrixUnit 1 3 central
  | _ => 1

def positiveMatrix (kind : Kind) (q : ℕ) {K : Type} [Field K]
    (root : PositiveRoot) (parameter central : K) : Matrix (Coord kind) (Coord kind) K :=
  match kind with
  | .L3 => linearRoot root parameter
  | .Sp4 => symplecticRoot root parameter
  | .U4 => unitaryRootFour q root parameter
  | .U5 => unitaryRootFive q root parameter central

def markedMatrix (kind : Kind) (q : ℕ) {K : Type} [Field K]
    (basis : GL (Coord kind) K) (root : PositiveRoot) (negative : Bool)
    (parameter central : K) : Matrix (Coord kind) (Coord kind) K :=
  (basis : Matrix (Coord kind) (Coord kind) K) *
    (if negative then (positiveMatrix kind q root parameter central).transpose
      else positiveMatrix kind q root parameter central) *
    ((basis⁻¹ : GL (Coord kind) K) : Matrix (Coord kind) (Coord kind) K)

def nativeRoot (kind : Kind) (q : ℕ) {K : Type} [Field K]
    (basis : GL (Coord kind) K) (root : PositiveRoot) (negative : Bool) :
    Subgroup (nativeGroup kind q K) :=
  Subgroup.closure {actor | RootAllowed kind root ∧ ∃ parameter central : K,
    ParameterAllowed kind q root parameter central ∧
    ((actor : nativeGroup kind q K) : GL (Coord kind) K).val =
      markedMatrix kind q basis root negative parameter central}

def projectiveMap (kind : Kind) (q : ℕ) (K : Type) [Field K] :
    nativeGroup kind q K →* StatedProj (nativeGroup kind q K) :=
  QuotientGroup.mk'
    ((StatedScalars (Coord kind) K).subgroupOf (nativeGroup kind q K))

structure Marking (kind : Kind) (p exponent : ℕ) (H : Type) [Group H] where
  field : Type
  fieldStructure : Field field
  finiteField : Finite field
  prime : p.Prime
  exponent_pos : 1 ≤ exponent
  field_card : @Nat.card field =
    if kind = .U4 ∨ kind = .U5 then (p ^ exponent) ^ 2 else p ^ exponent
  basis : letI := fieldStructure; GL (Coord kind) field
  basis_compatible : letI := fieldStructure; BasisCompatible kind (p ^ exponent) field basis
  identification : @StatedProj (Coord kind) _ _ field fieldStructure
    (@nativeGroup kind (p ^ exponent) field fieldStructure) ≃* H

attribute [instance] Marking.fieldStructure Marking.finiteField

def Marking.transport {kind : Kind} {p exponent : ℕ} {H : Type} [Group H]
    (marking : Marking kind p exponent H) :
    nativeGroup kind (p ^ exponent) marking.field →* H :=
  marking.identification.toMonoidHom.comp (projectiveMap kind (p ^ exponent) marking.field)

def Marking.parabolic {kind : Kind} {p exponent : ℕ} {H : Type} [Group H]
    (marking : Marking kind p exponent H) (second : Bool) : Subgroup H :=
  (nativeParabolic kind (p ^ exponent) marking.field marking.basis second).map marking.transport

def Marking.borel {kind : Kind} {p exponent : ℕ} {H : Type} [Group H]
    (marking : Marking kind p exponent H) : Subgroup H :=
  (nativeBorel kind (p ^ exponent) marking.field marking.basis).map marking.transport

def Marking.root {kind : Kind} {p exponent : ℕ} {H : Type} [Group H]
    (marking : Marking kind p exponent H) (root : PositiveRoot) (negative : Bool) : Subgroup H :=
  (nativeRoot kind (p ^ exponent) marking.basis root negative).map marking.transport


end CFSG.ASVolI.ChF.ClassicalRoots


namespace CFSG.ASVolI.ChF.G2Native

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable (K : Type) [Field K]

abbrev Parent := ↥(adjointGroup Tag.G2 K)

abbrev Lattice := Fin 2 → ℤ

def simpleVector (index : Fin 2) : Lattice := Pi.single index 1

def reflectedVector (word : List (Fin 2)) (vector : Lattice) : Lattice :=
  word.foldl (fun root index => reflect Tag.G2 index root) vector

def weylOperator (index : Fin 2) (parameter : Kˣ) :
    Module.End K (RootModule Tag.G2 K) :=
  xOp Tag.G2 K index (parameter : K) *
    yOp Tag.G2 K index (-(↑parameter⁻¹ : K)) *
    xOp Tag.G2 K index (parameter : K)

def weylWordOperator (word : List (Fin 2)) :
    Module.End K (RootModule Tag.G2 K) :=
  word.foldl (fun operator index => weylOperator K index 1 * operator) 1

def simpleGenerators (index : Fin 2) : Set (Parent K) :=
  {element | ∃ parameter : K,
    (element.1 : Module.End K (RootModule Tag.G2 K)) = xOp Tag.G2 K index parameter}

def rootGenerators (root : Lattice) : Set (Parent K) :=
  {element | ∃ word : List (Fin 2), ∃ index : Fin 2,
    reflectedVector word (simpleVector index) = root ∧
    ∃ representative : Parent K,
      (representative.1 : Module.End K (RootModule Tag.G2 K)) =
        weylWordOperator K word ∧
      ∃ generator ∈ simpleGenerators K index,
        element = representative * generator * representative⁻¹}

def rootSubgroup (root : Lattice) : Subgroup (Parent K) :=
  Subgroup.closure (rootGenerators K root)

def torusGenerators : Set (Parent K) :=
  {element | ∃ index : Fin 2, ∃ parameter : Kˣ,
    (element.1 : Module.End K (RootModule Tag.G2 K)) =
      weylOperator K index parameter * weylOperator K index (-1)}

def positiveBorel : Subgroup (Parent K) :=
  Subgroup.closure (torusGenerators K ∪
    {element | ∃ root : Lattice,
      0 < height (τ := Tag.G2) root ∧ element ∈ rootGenerators K root})

def pointParabolic : Subgroup (Parent K) :=
  positiveBorel K ⊔ rootSubgroup K (-simpleVector 1)

def lineParabolic : Subgroup (Parent K) :=
  positiveBorel K ⊔ rootSubgroup K (-simpleVector 0)

def highestLong : Lattice := ![2, 3]

def highestShort : Lattice := ![1, 2]

def longRoot : Subgroup (Parent K) := rootSubgroup K highestLong

def shortRoot : Subgroup (Parent K) := rootSubgroup K highestShort

abbrev Derived := ↥⁅adjointGroup Tag.G2 K, adjointGroup Tag.G2 K⁆

def derivedInclusion : Derived K →* Parent K where
  toFun element := ⟨element.1,
    ((Subgroup.commutator_le_sup _ _).trans (sup_le le_rfl le_rfl)) element.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def derivedLocal (localSubgroup : Subgroup (Parent K)) : Subgroup (Derived K) :=
  localSubgroup.comap (derivedInclusion K)

abbrev FullModel := AdjointQuotient Tag.G2 K

abbrev SmallModel := CFSG.Blueprint.DerivedCentralQuotient (adjointGroup Tag.G2 K)

def fullLocal (localSubgroup : Subgroup (Parent K)) : Subgroup (FullModel K) :=
  localSubgroup.map (QuotientGroup.mk' (Subgroup.center (Parent K)))

def smallLocal (localSubgroup : Subgroup (Parent K)) : Subgroup (SmallModel K) :=
  (derivedLocal K localSubgroup).map
    (QuotientGroup.mk' (Subgroup.center (Derived K)))

variable {H : Type} [Group H]

def fullImage (marking : FullModel K ≃* H)
    (localSubgroup : Subgroup (Parent K)) : Subgroup H :=
  (fullLocal K localSubgroup).map marking.toMonoidHom

def smallImage (marking : SmallModel K ≃* H)
    (localSubgroup : Subgroup (Parent K)) : Subgroup H :=
  (smallLocal K localSubgroup).map marking.toMonoidHom


end CFSG.ASVolI.ChF.G2Native


namespace CFSG.ASVolI.ChF.ExceptionalRoots

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable (tag : Tag) (K : Type) [Field K]

@[expose] def weylOperator (index : Fin tag.rank) (parameter : Kˣ) :
    Module.End K (RootModule tag K) :=
  xOp tag K index parameter * yOp tag K index (-((parameter⁻¹ : Kˣ) : K)) *
    xOp tag K index parameter

@[expose] def weylWordOperator (word : List (Fin tag.rank)) :
    Module.End K (RootModule tag K) :=
  ((word.map fun index => weylOperator tag K index 1).reverse).prod

@[expose] def IsAbsoluteRootElement (root : Fin tag.rank → ℤ) (parameter : K)
    (element : ModGL tag K) : Prop :=
  ∃ (seed : Fin tag.rank) (word : List (Fin tag.rank)) (actor : ModGL tag K),
    word.foldl (fun root index => reflect tag index root) (Pi.single seed 1) = root ∧
    (actor : Module.End K (RootModule tag K)) = weylWordOperator tag K word ∧
    (element : Module.End K (RootModule tag K)) =
      (actor : Module.End K (RootModule tag K)) * xOp tag K seed parameter *
        (actor⁻¹ : ModGL tag K)

@[expose] def absoluteRoot (root : Fin tag.rank → ℤ) : Subgroup (ModGL tag K) :=
  Subgroup.closure {element | ∃ parameter, IsAbsoluteRootElement tag K root parameter element}

@[expose] def absolutePositive : Subgroup (ModGL tag K) :=
  ⨆ root ∈ {root | IsRoot tag root ∧ 0 < height (τ := tag) root}, absoluteRoot tag K root

@[expose] def absoluteTorus : Subgroup (ModGL tag K) :=
  Subgroup.closure {element | ∃ (index : Fin tag.rank) (parameter : Kˣ),
    (element : Module.End K (RootModule tag K)) =
      weylOperator tag K index parameter * weylOperator tag K index (-1)}

@[expose] def absoluteBorel : Subgroup (ModGL tag K) :=
  absolutePositive tag K ⊔ absoluteTorus tag K

@[expose] def relativeWeyl (word : List (Fin tag.rank)) : Subgroup (ModGL tag K) :=
  Subgroup.closure {element | (element : Module.End K (RootModule tag K)) =
    weylWordOperator tag K word}

variable (sigma : K →+* K)

@[expose] def trialitySeed : Fin 6 → Fin Tag.D4.rank → ℤ :=
  ![![1, 0, 0, 0], ![0, 0, 1, 0], ![1, 0, 1, 0], ![0, 1, 1, 1],
    ![1, 1, 1, 1], ![1, 1, 2, 1]]


@[expose] def trialityOrbitRoot (root : Fin Tag.D4.rank → ℤ) :
    Subgroup (ModGL Tag.D4 K) :=
  CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K sigma ⊓
    (⨆ index : Fin 3,
      absoluteRoot Tag.D4 K
        (permLattice (τ := Tag.D4) (TwistTag.D4.perm ^ (index : ℕ)) root))

@[expose] def trialitySingletonRoot (root : Fin Tag.D4.rank → ℤ) :
    Subgroup (ModGL Tag.D4 K) :=
  CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K sigma ⊓ absoluteRoot Tag.D4 K root

@[expose] def trialityPositiveRoot (index : Fin 6) : Subgroup (ModGL Tag.D4 K) :=
  if index = 0 ∨ index = 2 ∨ index = 3 then
    trialityOrbitRoot K sigma (trialitySeed index)
  else trialitySingletonRoot K sigma (trialitySeed index)

@[expose] def trialityBorel : Subgroup (ModGL Tag.D4 K) :=
  CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K sigma ⊓ absoluteBorel Tag.D4 K

@[expose] def TrialityScope (prime exponent : ℕ) : Prop :=
  prime.Prime ∧ 1 ≤ exponent ∧ Nat.card K = (prime ^ exponent) ^ 3 ∧
    ∀ parameter : K, sigma parameter = parameter ^ (prime ^ exponent)

@[expose] def trialityParabolic (index : Fin 2) : Subgroup (ModGL Tag.D4 K) :=
  trialityBorel K sigma ⊔
    (CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K sigma ⊓
      relativeWeyl Tag.D4 K (if index = 0 then [0, 1, 3] else [2]))


@[expose] def reeFourSeed : Fin 4 → Fin Tag.F4.rank → ℤ :=
  ![![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 1, 1, 0], ![0, 1, 2, 0]]


@[expose] def reeTwoRoot (exponent : ℕ) : Subgroup (ModGL Tag.F4 K) :=
  reeFixedGroup Tag.F4 K reeF4Perm
    (fun index => if index ∈ reeF4Long then 2 ^ exponent else 2 ^ (exponent + 1)) ⊓
      (absoluteRoot Tag.F4 K (Pi.single 0 1) ⊔
        absoluteRoot Tag.F4 K (Pi.single 3 1))


@[expose] def reeGroup (exponent : ℕ) : Subgroup (ModGL Tag.F4 K) :=
  reeFixedGroup Tag.F4 K reeF4Perm
    (fun index => if index ∈ reeF4Long then 2 ^ exponent else 2 ^ (exponent + 1))

@[expose] def ReeScope (exponent : ℕ) : Prop :=
  Nat.card K = 2 ^ (2 * exponent + 1)

@[expose] def reeBorel (exponent : ℕ) : Subgroup (ModGL Tag.F4 K) :=
  reeGroup K exponent ⊓ absoluteBorel Tag.F4 K

@[expose] def reeParabolic (exponent : ℕ) (index : Fin 2) : Subgroup (ModGL Tag.F4 K) :=
  reeBorel K exponent ⊔ (reeGroup K exponent ⊓
    relativeWeyl Tag.F4 K (if index = 0 then [0, 3] else [1, 2, 1, 2]))

@[expose] def fixedWeylConjugate (tag : Tag) (K : Type) [Field K]
    (model : Subgroup (ModGL tag K)) (word : List (Fin tag.rank))
    (root : Subgroup (ModGL tag K)) : Subgroup (ModGL tag K) :=
  Subgroup.closure {element | ∃ actor : ModGL tag K,
    actor ∈ model ∧
    (actor : Module.End K (RootModule tag K)) = weylWordOperator tag K word ∧
    ∃ generator ∈ root, element = actor * generator * actor⁻¹}


@[expose] def trialityLongRoot : Subgroup (ModGL Tag.D4 K) :=
  fixedWeylConjugate Tag.D4 K (CFSG.Blueprint.twistedFixedGroup .D4 K sigma)
    [0, 1, 3, 2] (trialityPositiveRoot K sigma 1)

@[expose] def trialityShortRoot : Subgroup (ModGL Tag.D4 K) :=
  fixedWeylConjugate Tag.D4 K (CFSG.Blueprint.twistedFixedGroup .D4 K sigma)
    [2, 0, 1, 3] (trialityPositiveRoot K sigma 0)


@[expose] def reeMiddleCentralRoot (exponent : ℕ) : Subgroup (ModGL Tag.F4 K) :=
  reeGroup K exponent ⊓
    (absoluteRoot Tag.F4 K (reeFourSeed 2) ⊔
      absoluteRoot Tag.F4 K (reeFourSeed 3))

@[expose] def reeLongRoot (exponent : ℕ) : Subgroup (ModGL Tag.F4 K) :=
  fixedWeylConjugate Tag.F4 K (reeGroup K exponent)
    [0, 3, 1, 2, 1, 2, 0, 3] (reeMiddleCentralRoot K exponent)

@[expose] def reeShortRoot (exponent : ℕ) : Subgroup (ModGL Tag.F4 K) :=
  fixedWeylConjugate Tag.F4 K (reeGroup K exponent)
    [1, 2, 1, 2, 0, 3, 1, 2, 1, 2] (reeTwoRoot K exponent)

variable {Ambient : Type} [Group Ambient]

@[expose] def restrictRoot (model root : Subgroup Ambient) : Subgroup model :=
  root.comap model.subtype

@[expose] def centralImage (model root : Subgroup Ambient) :
    Subgroup (model ⧸ Subgroup.center model) :=
  (restrictRoot model root).map (QuotientGroup.mk' (Subgroup.center model))

@[expose] def derivedImage (model root : Subgroup Ambient) :
    Subgroup (CFSG.Blueprint.DerivedCentralQuotient model) :=
  (root.comap (⁅model, model⁆ : Subgroup Ambient).subtype).map
    (QuotientGroup.mk' (Subgroup.center ↥⁅model, model⁆))

variable {Model GroupTarget : Type} [Group Model] [Group GroupTarget]


end CFSG.ASVolI.ChF.ExceptionalRoots


namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion


@[expose] def classicalKind : ClassicalRoots.Kind → GLKind
  | .L3 => .L3
  | .Sp4 => .Sp4
  | .U4 => .U4
  | .U5 => .U5

structure NativeChart (kind : GLKind) (prime degree : ℕ)
    {E : Type} [Group E] (core : Subgroup E) where
  borel : Subgroup E
  points : Subgroup E
  lines : Subgroup E
  longRoot : Subgroup E
  shortRoot : Subgroup E
  coordinates :
    (∃ classical : ClassicalRoots.Kind, kind = classicalKind classical ∧
      ∃ marking : ClassicalRoots.Marking classical prime degree core,
        borel = marking.borel.map core.subtype ∧
        points = (marking.parabolic false).map core.subtype ∧
        lines = (marking.parabolic true).map core.subtype ∧
        longRoot = (marking.root (if classical = .L3 then .a13 else .longOne) false).map core.subtype ∧
        shortRoot = (marking.root (if classical = .L3 then .a12 else .sum) false).map core.subtype) ∨
    (kind = .G2 ∧ prime.Prime ∧ 1 ≤ degree ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = prime ^ degree ∧
      ∃ marking : G2Native.FullModel K ≃* core,
        borel = (G2Native.fullImage K marking (G2Native.positiveBorel K)).map core.subtype ∧
        points = (G2Native.fullImage K marking (G2Native.pointParabolic K)).map core.subtype ∧
        lines = (G2Native.fullImage K marking (G2Native.lineParabolic K)).map core.subtype ∧
        longRoot = (G2Native.fullImage K marking (G2Native.longRoot K)).map core.subtype ∧
        shortRoot = (G2Native.fullImage K marking (G2Native.shortRoot K)).map core.subtype) ∨
    (kind = .G2d ∧ prime = 2 ∧ degree = 1 ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      ∃ marking : G2Native.SmallModel K ≃* core,
        borel = (G2Native.smallImage K marking (G2Native.positiveBorel K)).map core.subtype ∧
        points = (G2Native.smallImage K marking (G2Native.pointParabolic K)).map core.subtype ∧
        lines = (G2Native.smallImage K marking (G2Native.lineParabolic K)).map core.subtype ∧
        longRoot = (G2Native.smallImage K marking (G2Native.longRoot K)).map core.subtype ∧
        shortRoot = (G2Native.smallImage K marking (G2Native.shortRoot K)).map core.subtype) ∨
    (kind = .D4tw ∧ prime.Prime ∧ 1 ≤ degree ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (sigma : K →+* K),
        ExceptionalRoots.TrialityScope K sigma prime degree ∧
      ∃ marking : CFSG.Blueprint.DerivedCentralQuotient (CFSG.Blueprint.twistedFixedGroup .D4 K sigma) ≃* core,
        borel = ((ExceptionalRoots.derivedImage (CFSG.Blueprint.twistedFixedGroup .D4 K sigma)
          (ExceptionalRoots.trialityBorel K sigma)).map marking.toMonoidHom).map core.subtype ∧
        points = ((ExceptionalRoots.derivedImage (CFSG.Blueprint.twistedFixedGroup .D4 K sigma)
          (ExceptionalRoots.trialityParabolic K sigma 0)).map marking.toMonoidHom).map core.subtype ∧
        lines = ((ExceptionalRoots.derivedImage (CFSG.Blueprint.twistedFixedGroup .D4 K sigma)
          (ExceptionalRoots.trialityParabolic K sigma 1)).map marking.toMonoidHom).map core.subtype ∧
        longRoot = ((ExceptionalRoots.derivedImage (CFSG.Blueprint.twistedFixedGroup .D4 K sigma)
          (ExceptionalRoots.trialityLongRoot K sigma)).map marking.toMonoidHom).map core.subtype ∧
        shortRoot = ((ExceptionalRoots.derivedImage (CFSG.Blueprint.twistedFixedGroup .D4 K sigma)
          (ExceptionalRoots.trialityShortRoot K sigma)).map marking.toMonoidHom).map core.subtype) ∨
    (prime = 2 ∧ ∃ exponent : ℕ,
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
        ExceptionalRoots.ReeScope K exponent ∧
        ((kind = .F4tw ∧ degree = 2 * exponent + 1 ∧
          ∃ marking : (ExceptionalRoots.reeGroup K exponent ⧸
              Subgroup.center (ExceptionalRoots.reeGroup K exponent)) ≃* core,
            borel = ((ExceptionalRoots.centralImage (ExceptionalRoots.reeGroup K exponent)
              (ExceptionalRoots.reeBorel K exponent)).map marking.toMonoidHom).map core.subtype ∧
            points = ((ExceptionalRoots.centralImage (ExceptionalRoots.reeGroup K exponent)
              (ExceptionalRoots.reeParabolic K exponent 1)).map marking.toMonoidHom).map core.subtype ∧
            lines = ((ExceptionalRoots.centralImage (ExceptionalRoots.reeGroup K exponent)
              (ExceptionalRoots.reeParabolic K exponent 0)).map marking.toMonoidHom).map core.subtype ∧
            longRoot = ((ExceptionalRoots.centralImage (ExceptionalRoots.reeGroup K exponent)
              (ExceptionalRoots.reeLongRoot K exponent)).map marking.toMonoidHom).map core.subtype ∧
            shortRoot = ((ExceptionalRoots.centralImage (ExceptionalRoots.reeGroup K exponent)
              (ExceptionalRoots.reeShortRoot K exponent)).map marking.toMonoidHom).map core.subtype) ∨
        (kind = .Tits ∧ degree = 1 ∧ exponent = 0 ∧
          ∃ marking : CFSG.Blueprint.DerivedCentralQuotient (ExceptionalRoots.reeGroup K exponent) ≃* core,
            borel = ((ExceptionalRoots.derivedImage (ExceptionalRoots.reeGroup K exponent)
              (ExceptionalRoots.reeBorel K exponent)).map marking.toMonoidHom).map core.subtype ∧
            points = ((ExceptionalRoots.derivedImage (ExceptionalRoots.reeGroup K exponent)
              (ExceptionalRoots.reeParabolic K exponent 1)).map marking.toMonoidHom).map core.subtype ∧
            lines = ((ExceptionalRoots.derivedImage (ExceptionalRoots.reeGroup K exponent)
              (ExceptionalRoots.reeParabolic K exponent 0)).map marking.toMonoidHom).map core.subtype ∧
            longRoot = ((ExceptionalRoots.derivedImage (ExceptionalRoots.reeGroup K exponent)
              (ExceptionalRoots.reeLongRoot K exponent)).map marking.toMonoidHom).map core.subtype ∧
            shortRoot = ((ExceptionalRoots.derivedImage (ExceptionalRoots.reeGroup K exponent)
              (ExceptionalRoots.reeShortRoot K exponent)).map marking.toMonoidHom).map core.subtype)))


inductive NativeCoordinates (kind : GLKind) (prime degree : ℕ)
    (H : Type) [Group H]
  | classical (classical : ClassicalRoots.Kind) (kind_eq : kind = classicalKind classical)
      (marking : ClassicalRoots.Marking classical prime degree H)
  | g2 (kind_eq : kind = .G2) (prime_ok : prime.Prime) (degree_pos : 1 ≤ degree)
      (K : Type) [Field K] [Finite K] (card : Nat.card K = prime ^ degree)
      (identification : G2Native.FullModel K ≃* H)
  | g2Derived (kind_eq : kind = .G2d) (prime_eq : prime = 2) (degree_eq : degree = 1)
      (K : Type) [Field K] [Finite K] (card : Nat.card K = 2)
      (identification : G2Native.SmallModel K ≃* H)
  | triality (kind_eq : kind = .D4tw) (K : Type) [Field K] [Finite K]
      (sigma : K →+* K) (scope : ExceptionalRoots.TrialityScope K sigma prime degree)
      (identification : CFSG.Blueprint.DerivedCentralQuotient (CFSG.Blueprint.twistedFixedGroup .D4 K sigma) ≃* H)
  | ree (kind_eq : kind = .F4tw) (prime_eq : prime = 2)
      (exponent : ℕ) (degree_eq : degree = 2 * exponent + 1)
      (K : Type) [Field K] [Finite K] [CharP K 2]
      (scope : ExceptionalRoots.ReeScope K exponent)
      (identification : (ExceptionalRoots.reeGroup K exponent ⧸
        Subgroup.center (ExceptionalRoots.reeGroup K exponent)) ≃* H)
  | tits (kind_eq : kind = .Tits) (prime_eq : prime = 2) (degree_eq : degree = 1)
      (K : Type) [Field K] [Finite K] [CharP K 2]
      (scope : ExceptionalRoots.ReeScope K 0)
      (identification : CFSG.Blueprint.DerivedCentralQuotient (ExceptionalRoots.reeGroup K 0) ≃* H)

namespace NativeCoordinates


end NativeCoordinates


def NativeChart.Matches {kind : GLKind} {prime degree : ℕ}
    {E : Type} [Group E] {core : Subgroup E} (chart : NativeChart kind prime degree core)
    (first second : Subgroup E) : Prop :=
  core ⊓ (first ⊓ second) = chart.borel ∧
    core ⊓ first = chart.points ∧ core ⊓ second = chart.lines


structure HypF_4_4g (κ : GLKind) (p f : ℕ) {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) : Prop where
  finite : Finite E
  model : IsGenLie ↥Gp κ p f
  normal : Gp.Normal
  centralizer_trivial : Subgroup.centralizer (Gp : Set E) = ⊥
  gen : M₁ ⊔ M₂ = ⊤
  lie_amalgam : ∃ chart : NativeChart κ p f Gp, chart.Matches M₁ M₂
  split : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h
  dynkin : ∀ g : E, g ∈ Subgroup.normalizer ((Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) : Set E) →
    g ∈ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E)


noncomputable def HypF_4_4g.chart {κ : GLKind} {p f : ℕ}
    {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g κ p f Gp M₁ M₂) : NativeChart κ p f Gp :=
  Classical.choose hyp.lie_amalgam


abbrev Cpl {E : Type} [Group E] (M₁ M₂ : Subgroup E) (Y : Type) [Group Y] : Type :=
  (RankTwoAmalgam.ofSubgroups M₁ M₂).Completion Y

section Notation

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]

@[expose] noncomputable def Qx (p : ℕ) (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) : Subgroup β.G0 :=
  ((pCoreOf p (Gp ⊓ M₁)).subgroupOf M₁).map (f1 (c := β))

@[expose] noncomputable def Ql (p : ℕ) (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) : Subgroup β.G0 :=
  ((pCoreOf p (Gp ⊓ M₂)).subgroupOf M₂).map (f2 (c := β))


@[expose] noncomputable def Sp (p : ℕ) (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) : Subgroup β.G0 :=
  (((pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))).subgroupOf (M₁ ⊓ M₂)).map
      (RankTwoAmalgam.ofSubgroups M₁ M₂).α1).map (f1 (c := β))


@[expose] def pathOrbit {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] {c : α.Completion Z} {n : ℕ}
    (H : Subgroup c.G0) (q : GPath c.graph n) : Set (GPath c.graph n) :=
  {r | ∃ g ∈ H, g • q = r}

end Notation

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion


end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def pointwiseStab {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z)
    (S : Set c.Γ) : Subgroup c.G0 :=
  ⨅ v ∈ S, stv c v


end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion


end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section F418

variable {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z)


end F418

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def ctr {E : Type} [Group E] (K : Subgroup E) : Subgroup E :=
  K ⊓ Subgroup.centralizer (K : Set E)


end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section F431World

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]


end F431World


end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Open CFSG.Quasithin


end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section F423

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}


variable {Y : Type} [Group Y]


end F423

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


end CFSG.ASVolI

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section FieldGraph

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {E : Type} [Group E]


def NativeRepresentativeAction {Representatives Model : Type}
    [Group Representatives] [Group Model] (Gp : Subgroup E)
    (quotient : Representatives →* Model) (identification : Model ≃* Gp)
    (operator : Representatives → Representatives → Prop) (actor : E) : Prop :=
  ∀ representative, ∃ image, operator representative image ∧
    (identification (quotient image) : E) =
      actor * (identification (quotient representative) : E) * actor⁻¹


def NativeCoordinates.PureGraphAction {kind : GLKind} {degree : ℕ} {Gp : Subgroup E}
    (coordinates : NativeCoordinates kind 2 degree Gp) (actor : E) : Prop :=
  match coordinates with
  | .classical modelKind _ marking =>
      (modelKind = .U4 ∨ modelKind = .U5) ∧
      ∃ sigma : marking.field →+* marking.field,
        (∀ parameter, sigma parameter = parameter ^ (2 ^ degree)) ∧
        NativeRepresentativeAction Gp
          (ClassicalRoots.projectiveMap modelKind (2 ^ degree) marking.field)
          marking.identification
          (fun source target =>
            (target : Matrix.GeneralLinearGroup (ClassicalRoots.Coord modelKind)
              marking.field) =
            marking.basis * Matrix.GeneralLinearGroup.map sigma
              (marking.basis⁻¹ *
                (source : Matrix.GeneralLinearGroup (ClassicalRoots.Coord modelKind)
                  marking.field) * marking.basis) * marking.basis⁻¹) actor
  | _ => False


def NativeCoordinates.transport {kind : GLKind} {prime degree : ℕ}
    {H H' : Type} [Group H] [Group H']
    (coordinates : NativeCoordinates kind prime degree H) (comparison : H ≃* H') :
    NativeCoordinates kind prime degree H' :=
  match coordinates with
  | .classical modelKind kind_eq marking =>
      .classical modelKind kind_eq
        { marking with identification := marking.identification.trans comparison }
  | @NativeCoordinates.g2 _ _ _ _ _ kind_eq prime_ok degree_pos K fieldK finiteK card identification =>
      letI := fieldK
      letI := finiteK
      .g2 kind_eq prime_ok degree_pos K card (identification.trans comparison)
  | @NativeCoordinates.g2Derived _ _ _ _ _ kind_eq prime_eq degree_eq K fieldK finiteK card identification =>
      letI := fieldK
      letI := finiteK
      .g2Derived kind_eq prime_eq degree_eq K card (identification.trans comparison)
  | @NativeCoordinates.triality _ _ _ _ _ kind_eq K fieldK finiteK sigma scope identification =>
      letI := fieldK
      letI := finiteK
      .triality kind_eq K sigma scope (identification.trans comparison)
  | @NativeCoordinates.ree _ _ _ _ _ kind_eq prime_eq exponent degree_eq K fieldK finiteK charK scope identification =>
      letI := fieldK
      letI := finiteK
      letI := charK
      .ree kind_eq prime_eq exponent degree_eq K scope (identification.trans comparison)
  | @NativeCoordinates.tits _ _ _ _ _ kind_eq prime_eq degree_eq K fieldK finiteK charK scope identification =>
      letI := fieldK
      letI := finiteK
      letI := charK
      .tits kind_eq prime_eq degree_eq K scope (identification.trans comparison)

def NativeCoordinates.InnerDiagonal {kind : GLKind} {degree : ℕ} {Gp : Subgroup E}
    (coordinates : NativeCoordinates kind 2 degree Gp) (conjugacy : MulAut Gp) : Prop :=
  match coordinates with
  | .classical modelKind _ marking =>
      ∃ matrix : Matrix.GeneralLinearGroup (ClassicalRoots.Coord modelKind) marking.field,
        (ClassicalRoots.nativeGroup modelKind (2 ^ degree) marking.field).map
          (MulAut.conj matrix).toMonoidHom =
            ClassicalRoots.nativeGroup modelKind (2 ^ degree) marking.field ∧
        ∀ representative : ClassicalRoots.nativeGroup modelKind (2 ^ degree) marking.field,
          ∃ image : ClassicalRoots.nativeGroup modelKind (2 ^ degree) marking.field,
            (image : Matrix.GeneralLinearGroup (ClassicalRoots.Coord modelKind) marking.field) =
              matrix * representative * matrix⁻¹ ∧
            marking.transport image = conjugacy (marking.transport representative)
  | _ => ∃ element : Gp, conjugacy = MulAut.conj element


def NativeCoordinates.GraphAction {kind : GLKind} {degree : ℕ} {Gp : Subgroup E}
    (coordinates : NativeCoordinates kind 2 degree Gp) (actor : E) : Prop :=
  ∃ conjugacy : MulAut Gp, coordinates.InnerDiagonal conjugacy ∧
    (coordinates.transport conjugacy).PureGraphAction actor


end FieldGraph

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam

variable {E Y : Type} [Group E] [Group Y]


@[expose] def f437Ebar (fb : E) : Subgroup E :=
  Subgroup.centralizer ({fb} : Set E)


end CFSG.ASVolI.ChF

namespace CFSG.ASVolI


open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion ChF


end CFSG.ASVolI

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF.G2Native

variable (K : Type) [Field K] {H : Type} [Group H]


end CFSG.ASVolI.ChF.G2Native

namespace CFSG.ASVolI.ChF.NativeFrame

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam

structure OrderedDictionary (Model : Type) [Group Model] where
  borel : Subgroup Model
  pointParabolic : Subgroup Model
  lineParabolic : Subgroup Model
  longRoot : Subgroup Model
  shortRoot : Subgroup Model

variable {Model E Y : Type} [Group Model] [Group E] [Group Y]

structure Marking (native : OrderedDictionary Model) (core : Subgroup E) where
  equivalence : Model ≃* core

def Marking.embedding {native : OrderedDictionary Model} {core : Subgroup E}
    (marking : Marking native core) : Model →* E :=
  core.subtype.comp marking.equivalence.toMonoidHom

def Marking.image {native : OrderedDictionary Model} {core : Subgroup E}
    (marking : Marking native core) (localSubgroup : Subgroup Model) : Subgroup E :=
  localSubgroup.map marking.embedding

def Marking.borel {native : OrderedDictionary Model} {core : Subgroup E}
    (marking : Marking native core) : Subgroup E := marking.image native.borel


def Marking.lines {native : OrderedDictionary Model} {core : Subgroup E}
    (marking : Marking native core) : Subgroup E := marking.image native.lineParabolic

def Marking.longRoot {native : OrderedDictionary Model} {core : Subgroup E}
    (marking : Marking native core) : Subgroup E := marking.image native.longRoot

def Marking.shortRoot {native : OrderedDictionary Model} {core : Subgroup E}
    (marking : Marking native core) : Subgroup E := marking.image native.shortRoot


variable (K : Type) [Field K]

def classical {kind : ClassicalRoots.Kind} {p exponent : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking kind p exponent H) : OrderedDictionary H where
  borel := marking.borel
  pointParabolic := marking.parabolic false
  lineParabolic := marking.parabolic true
  longRoot := marking.root (if kind = .L3 then .a13 else .longOne) false
  shortRoot := marking.root (if kind = .L3 then .a12 else .sum) false

def triality (sigma : K →+* K) : OrderedDictionary
    (CFSG.Blueprint.DerivedCentralQuotient (CFSG.Blueprint.twistedFixedGroup .D4 K sigma)) where
  borel := ExceptionalRoots.derivedImage _ (ExceptionalRoots.trialityBorel K sigma)
  pointParabolic := ExceptionalRoots.derivedImage _ (ExceptionalRoots.trialityParabolic K sigma 0)
  lineParabolic := ExceptionalRoots.derivedImage _ (ExceptionalRoots.trialityParabolic K sigma 1)
  longRoot := ExceptionalRoots.derivedImage _ (ExceptionalRoots.trialityLongRoot K sigma)
  shortRoot := ExceptionalRoots.derivedImage _ (ExceptionalRoots.trialityShortRoot K sigma)

def ree (exponent : ℕ) : OrderedDictionary
    ((ExceptionalRoots.reeGroup K exponent) ⧸
      Subgroup.center (ExceptionalRoots.reeGroup K exponent)) where
  borel := ExceptionalRoots.centralImage _ (ExceptionalRoots.reeBorel K exponent)
  pointParabolic := ExceptionalRoots.centralImage _ (ExceptionalRoots.reeParabolic K exponent 1)
  lineParabolic := ExceptionalRoots.centralImage _ (ExceptionalRoots.reeParabolic K exponent 0)
  longRoot := ExceptionalRoots.centralImage _ (ExceptionalRoots.reeLongRoot K exponent)
  shortRoot := ExceptionalRoots.centralImage _ (ExceptionalRoots.reeShortRoot K exponent)

def tits : OrderedDictionary
    (CFSG.Blueprint.DerivedCentralQuotient (ExceptionalRoots.reeGroup K 0)) where
  borel := ExceptionalRoots.derivedImage _ (ExceptionalRoots.reeBorel K 0)
  pointParabolic := ExceptionalRoots.derivedImage _ (ExceptionalRoots.reeParabolic K 0 1)
  lineParabolic := ExceptionalRoots.derivedImage _ (ExceptionalRoots.reeParabolic K 0 0)
  longRoot := ExceptionalRoots.derivedImage _ (ExceptionalRoots.reeLongRoot K 0)
  shortRoot := ExceptionalRoots.derivedImage _ (ExceptionalRoots.reeShortRoot K 0)


def titsParentAssemblyGoal : Prop :=
  ExceptionalRoots.ReeScope K 0 →
    let full := ree K 0
    let small := tits K
    IsLieParabolics 2 (⊤ : Subgroup
      (CFSG.Blueprint.DerivedCentralQuotient (ExceptionalRoots.reeGroup K 0)))
      small.borel small.pointParabolic small.lineParabolic ∧
    small.borel.relIndex small.pointParabolic = 5 ∧
    small.borel.relIndex small.lineParabolic = 3 ∧
    ∃ inclusion : CFSG.Blueprint.DerivedCentralQuotient (ExceptionalRoots.reeGroup K 0) →*
        (ExceptionalRoots.reeGroup K 0 ⧸
          Subgroup.center (ExceptionalRoots.reeGroup K 0)),
      Function.Injective inclusion ∧ inclusion.range.index = 2 ∧
      (∀ derivedRepresentative : ↥⁅ExceptionalRoots.reeGroup K 0,
          ExceptionalRoots.reeGroup K 0⁆,
        ∀ parentRepresentative : ExceptionalRoots.reeGroup K 0,
          (parentRepresentative : CFSG.Blueprint.Chevalley.ModGL
            CFSG.Blueprint.Chevalley.Tag.F4 K) = derivedRepresentative.val →
          inclusion (QuotientGroup.mk derivedRepresentative) =
            QuotientGroup.mk parentRepresentative) ∧
      small.borel.map inclusion = inclusion.range ⊓ full.borel ∧
      small.pointParabolic.map inclusion = inclusion.range ⊓ full.pointParabolic ∧
      small.lineParabolic.map inclusion = inclusion.range ⊓ full.lineParabolic ∧
      small.longRoot.map inclusion = inclusion.range ⊓ full.longRoot ∧
      small.shortRoot.map inclusion = inclusion.range ⊓ full.shortRoot ∧
      (small.borel.map inclusion).relIndex full.borel = 2 ∧
      (small.pointParabolic.map inclusion).relIndex full.pointParabolic = 2 ∧
      (small.lineParabolic.map inclusion).relIndex full.lineParabolic = 2

end CFSG.ASVolI.ChF.NativeFrame

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion


end CFSG.ASVolI.ChF

namespace CFSG.ASVolI.ChF

open CFSG.Open


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4a_two_lt_encard_nbrs {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    {c : α.Completion Y} (hc : c.IsFaithful) (h1 : 2 ≤ α.qOne) (h2 : 2 ≤ α.qTwo) :
    2 < (CosetGeom.nbrs c.xv).encard ∧ 2 < (CosetGeom.nbrs c.lv).encard := by
  have e1 := nbrs_xv_card (c := c) hc
  have e2 := nbrs_lv_card (c := c) hc
  unfold RankTwoAmalgam.qOne at h1
  unfold RankTwoAmalgam.qTwo at h2
  have n1 : (CosetGeom.nbrs c.xv).ncard = α.α1.range.index := by
    rw [← Nat.card_coe_set_eq]; exact e1
  have n2 : (CosetGeom.nbrs c.lv).ncard = α.α2.range.index := by
    rw [← Nat.card_coe_set_eq]; exact e2
  have hfin1 : (CosetGeom.nbrs c.xv).Finite := Set.finite_of_ncard_pos (by omega)
  have hfin2 : (CosetGeom.nbrs c.lv).Finite := Set.finite_of_ncard_pos (by omega)
  have a1 : (CosetGeom.nbrs c.xv).encard = ((CosetGeom.nbrs c.xv).ncard : ℕ∞) :=
    (hfin1.cast_ncard_eq).symm
  have a2 : (CosetGeom.nbrs c.lv).encard = ((CosetGeom.nbrs c.lv).ncard : ℕ∞) :=
    (hfin2.cast_ncard_eq).symm
  refine ⟨?_, ?_⟩
  · rw [a1, n1]
    exact_mod_cast (by omega : 2 < α.α1.range.index)
  · rw [a2, n2]
    exact_mod_cast (by omega : 2 < α.α2.range.index)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF4a_hval {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}
    (hc : c.IsFaithful) (h1 : 2 ≤ α.qOne) (h2 : 2 ≤ α.qTwo) :
    ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b := fun v a b =>
  CosetGeom.exists_nbr_ne (burnsideF4a_two_lt_encard_nbrs hc h1 h2).1
    (burnsideF4a_two_lt_encard_nbrs hc h1 h2).2 v a b


end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

universe u v w

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF in

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF in

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF in

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF in

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF in

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF in

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF in

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF in


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open


end CFSG.ASVolI.ChF

namespace CFSG.ASVolI.ChF


end CFSG.ASVolI.ChF
