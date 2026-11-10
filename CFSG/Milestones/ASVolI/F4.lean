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

@[expose] def IsLie (κ : GLKind) : Prop := κ ≠ G2d ∧ κ ≠ Tits

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

@[expose] def IsLongRootParabolic {E : Type} [Group E] (p : ℕ) (H P : Subgroup E) : Prop :=
  ∃ z : E, z ∈ oPPrime p P ∧ z ≠ 1 ∧ (∀ y ∈ oPPrime p P, y * z = z * y) ∧
    ∀ g ∈ H, g * z = z * g → g ∈ P

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

def locals {kind : GLKind} {prime degree : ℕ} {H : Type} [Group H]
    (coordinates : NativeCoordinates kind prime degree H) :
    Subgroup H × Subgroup H × Subgroup H × Subgroup H × Subgroup H :=
  match coordinates with
  | .classical modelKind _ marking =>
      (marking.borel, marking.parabolic false, marking.parabolic true,
        marking.root (if modelKind = .L3 then .a13 else .longOne) false,
        marking.root (if modelKind = .L3 then .a12 else .sum) false)
  | @NativeCoordinates.g2 _ _ _ _ _ _ _ _ K fieldK finiteK _ identification =>
      letI := fieldK
      letI := finiteK
      (G2Native.fullImage K identification (G2Native.positiveBorel K),
        G2Native.fullImage K identification (G2Native.pointParabolic K),
        G2Native.fullImage K identification (G2Native.lineParabolic K),
        G2Native.fullImage K identification (G2Native.longRoot K),
        G2Native.fullImage K identification (G2Native.shortRoot K))
  | @NativeCoordinates.g2Derived _ _ _ _ _ _ _ _ K fieldK finiteK _ identification =>
      letI := fieldK
      letI := finiteK
      (G2Native.smallImage K identification (G2Native.positiveBorel K),
        G2Native.smallImage K identification (G2Native.pointParabolic K),
        G2Native.smallImage K identification (G2Native.lineParabolic K),
        G2Native.smallImage K identification (G2Native.longRoot K),
        G2Native.smallImage K identification (G2Native.shortRoot K))
  | @NativeCoordinates.triality _ _ _ _ _ _ K fieldK finiteK sigma _ identification =>
      letI := fieldK
      letI := finiteK
      let image := fun localSubgroup =>
        (ExceptionalRoots.derivedImage (CFSG.Blueprint.twistedFixedGroup .D4 K sigma)
          localSubgroup).map identification.toMonoidHom
      (image (ExceptionalRoots.trialityBorel K sigma),
        image (ExceptionalRoots.trialityParabolic K sigma 0),
        image (ExceptionalRoots.trialityParabolic K sigma 1),
        image (ExceptionalRoots.trialityLongRoot K sigma),
        image (ExceptionalRoots.trialityShortRoot K sigma))
  | @NativeCoordinates.ree _ _ _ _ _ _ _ exponent _ K fieldK finiteK charK _ identification =>
      letI := fieldK
      letI := finiteK
      letI := charK
      let image := fun localSubgroup =>
        (ExceptionalRoots.centralImage (ExceptionalRoots.reeGroup K exponent)
          localSubgroup).map identification.toMonoidHom
      (image (ExceptionalRoots.reeBorel K exponent),
        image (ExceptionalRoots.reeParabolic K exponent 1),
        image (ExceptionalRoots.reeParabolic K exponent 0),
        image (ExceptionalRoots.reeLongRoot K exponent),
        image (ExceptionalRoots.reeShortRoot K exponent))
  | @NativeCoordinates.tits _ _ _ _ _ _ _ _ K fieldK finiteK charK _ identification =>
      letI := fieldK
      letI := finiteK
      letI := charK
      let image := fun localSubgroup =>
        (ExceptionalRoots.derivedImage (ExceptionalRoots.reeGroup K 0)
          localSubgroup).map identification.toMonoidHom
      (image (ExceptionalRoots.reeBorel K 0),
        image (ExceptionalRoots.reeParabolic K 0 1),
        image (ExceptionalRoots.reeParabolic K 0 0),
        image (ExceptionalRoots.reeLongRoot K 0),
        image (ExceptionalRoots.reeShortRoot K 0))

end NativeCoordinates

def NativeChart.PayloadFits {kind : GLKind} {prime degree : ℕ}
    {E : Type} [Group E] {core : Subgroup E}
    (chart : NativeChart kind prime degree core)
    (coordinates : NativeCoordinates kind prime degree core) : Prop :=
  let localSubgroups := coordinates.locals
  chart.borel = localSubgroups.1.map core.subtype ∧
    chart.points = localSubgroups.2.1.map core.subtype ∧
    chart.lines = localSubgroups.2.2.1.map core.subtype ∧
    chart.longRoot = localSubgroups.2.2.2.1.map core.subtype ∧
    chart.shortRoot = localSubgroups.2.2.2.2.map core.subtype

theorem NativeChart.payload_nonempty {kind : GLKind} {prime degree : ℕ}
    {E : Type} [Group E] {core : Subgroup E}
    (chart : NativeChart kind prime degree core) :
    Nonempty {coordinates : NativeCoordinates kind prime degree core //
      chart.PayloadFits coordinates} := by
  rcases chart.coordinates with
    ⟨c, hk, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, hp, hd, K, fK, finK, card, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, hp, hd, K, fK, finK, card, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, hp, hd, K, fK, finK, sigma, scope, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hp, exponent, K, fK, finK, charK, scope,
      ⟨hk, hd, marking, h1, h2, h3, h4, h5⟩ | ⟨hk, hd, he, marking, h1, h2, h3, h4, h5⟩⟩
  · exact ⟨⟨.classical c hk marking, h1, h2, h3, h4, h5⟩⟩
  · exact ⟨⟨.g2 hk hp hd K card marking, h1, h2, h3, h4, h5⟩⟩
  · exact ⟨⟨.g2Derived hk hp hd K card marking, h1, h2, h3, h4, h5⟩⟩
  · exact ⟨⟨.triality hk K sigma scope marking, h1, h2, h3, h4, h5⟩⟩
  · exact ⟨⟨.ree hk hp exponent hd K scope marking, h1, h2, h3, h4, h5⟩⟩
  · subst he
    exact ⟨⟨.tits hk hp hd K scope marking, h1, h2, h3, h4, h5⟩⟩

noncomputable def NativeChart.coordinatePayload {kind : GLKind} {prime degree : ℕ}
    {E : Type} [Group E] {core : Subgroup E}
    (chart : NativeChart kind prime degree core) :
    NativeCoordinates kind prime degree core :=
  (Classical.choice chart.payload_nonempty).1


def NativeChart.Matches {kind : GLKind} {prime degree : ℕ}
    {E : Type} [Group E] {core : Subgroup E} (chart : NativeChart kind prime degree core)
    (first second : Subgroup E) : Prop :=
  core ⊓ (first ⊓ second) = chart.borel ∧
    core ⊓ first = chart.points ∧ core ⊓ second = chart.lines

def NativeChart.RootInvolution {kind : GLKind} {prime degree : ℕ}
    {E : Type} [Group E] {core : Subgroup E} (chart : NativeChart kind prime degree core)
    (short : Bool) (element : E) : Prop :=
  element ∈ core ∧ element ≠ 1 ∧ element * element = 1 ∧
    (kind = .G2d → short = false) ∧
    ∃ conjugator ∈ core, conjugator * element * conjugator⁻¹ ∈
      if short then chart.shortRoot else chart.longRoot

def NativeChart.C2Involution {prime degree : ℕ}
    {E : Type} [Group E] {core : Subgroup E}
    (chart : NativeChart .Sp4 prime degree core) (element : E) : Prop :=
  element ∈ core ∧ element ≠ 1 ∧ element * element = 1 ∧
    ∃ conjugator ∈ core, ∃ long ∈ chart.longRoot, ∃ short ∈ chart.shortRoot,
      long ≠ 1 ∧ short ≠ 1 ∧ conjugator * element * conjugator⁻¹ = long * short


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


structure HypF_4_4 (κ : GLKind) (p f : ℕ) {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) : Prop
    extends HypF_4_4g κ p f Gp M₁ M₂ where
  canonical : (κ = GLKind.G2d ∨ κ = GLKind.Tits) → Gp = ⊤

@[expose] def IsLieExtAmalgam {E : Type} [Group E] (M₁ M₂ : Subgroup E) : Prop :=
  ∃ (κ' : GLKind) (p' f' : ℕ) (Gp' : Subgroup E), κ'.IsLie ∧ HypF_4_4 κ' p' f' Gp' M₁ M₂

@[expose] def IsLieExtBy (Ġ : Type) [Group Ġ] (Gq : Subgroup Ġ) (κ : GLKind) (p f : ℕ) : Prop :=
  IsGenLie ↥Gq κ p f ∧ Gq.Normal ∧ Subgroup.centralizer (Gq : Set Ġ) = ⊥ ∧
    ∃ B P₁ P₂ : Subgroup Ġ, IsLieParabolics p Gq B P₁ P₂ ∧
      ∀ g : Ġ, g ∈ Subgroup.normalizer (B : Set Ġ) → g ∈ Subgroup.normalizer (P₁ : Set Ġ)

@[expose] def IsLieExtGroup (Ġ : Type) [Group Ġ] (κ : GLKind) (p f : ℕ) : Prop :=
  ∃ Gq : Subgroup Ġ, IsLieExtBy Ġ Gq κ p f

abbrev Cpl {E : Type} [Group E] (M₁ M₂ : Subgroup E) (Y : Type) [Group Y] : Type :=
  (RankTwoAmalgam.ofSubgroups M₁ M₂).Completion Y

section Notation

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]

@[expose] noncomputable def Qx (p : ℕ) (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) : Subgroup β.G0 :=
  ((pCoreOf p (Gp ⊓ M₁)).subgroupOf M₁).map (f1 (c := β))

@[expose] noncomputable def Ql (p : ℕ) (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) : Subgroup β.G0 :=
  ((pCoreOf p (Gp ⊓ M₂)).subgroupOf M₂).map (f2 (c := β))

@[expose] noncomputable def Qu (p : ℕ) (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (u : β.Γ) : Subgroup β.G0 :=
  β.Qvert (Qx p Gp β) (Ql p Gp β) u

@[expose] noncomputable def Sp (p : ℕ) (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) : Subgroup β.G0 :=
  (((pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))).subgroupOf (M₁ ⊓ M₂)).map
      (RankTwoAmalgam.ofSubgroups M₁ M₂).α1).map (f1 (c := β))

@[expose] noncomputable def toE (ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂)) : ι.G0 →* E :=
  (M₁ ⊔ M₂).subtype.comp ((ι.φ1.range ⊔ ι.φ2.range).subtype)

@[expose] noncomputable def GpIn (Gp : Subgroup E) (ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂)) : Subgroup ι.G0 :=
  Gp.comap (toE ι)

@[expose] def pathOrbit {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] {c : α.Completion Z} {n : ℕ}
    (H : Subgroup c.G0) (q : GPath c.graph n) : Set (GPath c.graph n) :=
  {r | ∃ g ∈ H, g • q = r}

end Notation

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def vtx1 {E : Type} [Group E] {G₀ G₁ G₂ : Subgroup E} (g : ↥G₀) : CosetGeom G₀ G₁ G₂ :=
  Sum.inl (g : ↥G₀ ⧸ G₁.subgroupOf G₀)

@[expose] def vtx2 {E : Type} [Group E] {G₀ G₁ G₂ : Subgroup E} (g : ↥G₀) : CosetGeom G₀ G₁ G₂ :=
  Sum.inr (g : ↥G₀ ⧸ G₂.subgroupOf G₀)

@[expose] noncomputable def qOfType (α : RankTwoAmalgam.{0}) (b : Bool) : ℕ :=
  if b then α.qTwo else α.qOne

@[expose] def IsSimplex {V : Type} (Γ : SimpleGraph V) (s : Set V) : Prop :=
  (∃ u, s = {u}) ∨ ∃ u v, Γ.Adj u v ∧ s = {u, v}

@[expose] def pathVerts {V : Type} {Γ : SimpleGraph V} {n : ℕ} (q : GPath Γ n) : Set V :=
  {w | ∃ i ≤ n, q i = w}

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def F_4_5 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ →
    ∀ ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂), ι = incl M₁ M₂ →
    IsGenPolygon ι.graph κ.m ∧
    ((Gp = ⊤ ∧ (κ = .G2d ∨ κ = .Tits)) →
      ∃ (Gs : Type) (_ : Group Gs) (j : E →* Gs), Function.Injective j ∧ j.range.index = 2 ∧
        IsGenLie Gs (if κ = .G2d then .G2 else .F4tw) 2 1 ∧
        ∃ B₀ P₁ P₂ : Subgroup Gs, IsLieParabolics 2 ⊤ B₀ P₁ P₂ ∧ IsLongRootParabolic 2 ⊤ P₁ ∧
          M₁.map j = j.range ⊓ P₁ ∧ M₂.map j = j.range ⊓ P₂ ∧
          (M₁.map j).relIndex P₁ = 2 ∧ (M₂.map j).relIndex P₂ = 2 ∧
          ∃ φ : CosetGeom (M₁ ⊔ M₂) M₁ M₂ ≃ CosetGeom (⊤ : Subgroup Gs) P₁ P₂,
            (∀ a b, (CosetGeom.graph (⊤ : Subgroup Gs) P₁ P₂).Adj (φ a) (φ b) ↔
              (CosetGeom.graph (M₁ ⊔ M₂) M₁ M₂).Adj a b) ∧
            ∀ g : ↥(M₁ ⊔ M₂),
              φ (vtx1 g) = vtx1 ⟨j g, Subgroup.mem_top _⟩ ∧ φ (vtx2 g) = vtx2 ⟨j g, Subgroup.mem_top _⟩) ∧
    (∀ u v : ι.Γ, ι.graph.dist u v < κ.m →
      ∃! q : GPath ι.graph (ι.graph.dist u v),
        q 0 = u ∧ q (ι.graph.dist u v) = v ∧ q.IsGeodesic) ∧
    (∀ u v : ι.Γ, ι.graph.dist u v = κ.m →
      Nat.card ↥(ι.geods κ.m u v) = Nat.card ↥(CosetGeom.nbrs u) ∧
      ∀ S : Set ι.Γ, (u ∈ S ∧ v ∈ S ∧ ι.IsApartment κ.m S) ↔
        ∃ q₁ ∈ ι.geods κ.m u v, ∃ q₂ ∈ ι.geods κ.m u v, q₁ ≠ q₂ ∧ S = pathVerts q₁ ∪ pathVerts q₂) ∧
    (IsLieExtAmalgam M₁ M₂ → ∀ u v : ι.Γ, ι.graph.dist u v = κ.m →
      IsComplementIn (stv ι u ⊓ stv ι v) (Qu p Gp ι u) (stv ι u) ∧
      IsComplementIn (stv ι u ⊓ stv ι v) (Qu p Gp ι v) (stv ι v) ∧
      (∃ L₁ L₂ : Subgroup ι.G0, L₁ ≤ stv ι u ⊓ stv ι v ∧ L₂ ≤ stv ι u ⊓ stv ι v ∧
        IsComplementIn L₁ (Qu p Gp ι u) (GpIn Gp ι ⊓ stv ι u) ∧
        IsComplementIn L₂ (Qu p Gp ι v) (GpIn Gp ι ⊓ stv ι v)) ∧
      ∀ q₁ ∈ ι.geods κ.m u v, ∀ q₂ ∈ ι.geods κ.m u v, q₁ ≠ q₂ →
        ∀ r₁ ∈ ι.geods κ.m u v, ∀ r₂ ∈ ι.geods κ.m u v, r₁ ≠ r₂ →
          ∃ g ∈ stv ι u ⊓ stv ι v, g • q₁ = r₁ ∧ g • q₂ = r₂) ∧
    (Gp = ⊤ → ∀ u v : ι.Γ, ι.graph.Adj u v →
      Qu p Gp ι u ≤ oPPrime p (stv ι u ⊓ stv ι v) ∧
      (∀ w ∈ CosetGeom.nbrs u, ∀ q ∈ Qu p Gp ι u, q • w = w) ∧
      (∀ w₁ ∈ CosetGeom.nbrs u \ {v}, ∀ w₂ ∈ CosetGeom.nbrs u \ {v},
        ∃ g ∈ oPPrime p (stv ι u ⊓ stv ι v), g • w₁ = w₂) ∧
      (∀ g ∈ oPPrime p (stv ι u ⊓ stv ι v), ∀ w ∈ CosetGeom.nbrs u \ {v}, g • w = w →
        g ∈ Qu p Gp ι u) ∧
      Nat.card ↥(CosetGeom.nbrs u \ {v}) = qOfType (RankTwoAmalgam.ofSubgroups M₁ M₂)
        (CosetGeom.vtype u)) ∧
    (IsLieExtAmalgam M₁ M₂ → ∀ u : ι.Γ, ι.PathTrans u (κ.m + 1)) ∧
    ((Gp = ⊤ ∧ (κ = .Tits ∨ κ = .G2d)) →
      ι.PathTrans ι.xv κ.m ∧
      (ι.PathTrans ι.lv (κ.m - 1) ∧
        (∃ q₁ ∈ GPath.nbPaths ι.graph ι.lv κ.m, ∃ q₂ ∈ GPath.nbPaths ι.graph ι.lv κ.m,
          GPath.nbPaths ι.graph ι.lv κ.m =
            pathOrbit (stv ι ι.lv) q₁ ∪ pathOrbit (stv ι ι.lv) q₂ ∧
          Disjoint (pathOrbit (stv ι ι.lv) q₁) (pathOrbit (stv ι ι.lv) q₂) ∧
          Nat.card ↥(pathOrbit (stv ι ι.lv) q₁) = Nat.card ↥(pathOrbit (stv ι ι.lv) q₂)) ∧
        ∀ v ∈ CosetGeom.sphere κ.m ι.lv,
          ∀ q₁ ∈ GPath.nbPaths ι.graph ι.lv κ.m, q₁ κ.m = v →
          ∀ q₂ ∈ GPath.nbPaths ι.graph ι.lv κ.m, q₂ κ.m = v → q₁ ≠ q₂ →
          ∀ r₁ ∈ GPath.nbPaths ι.graph ι.lv κ.m, r₁ κ.m = v →
          ∀ r₂ ∈ GPath.nbPaths ι.graph ι.lv κ.m, r₂ κ.m = v → r₁ ≠ r₂ →
            ∃ g ∈ stv ι ι.lv ⊓ stv ι v, g • q₁ = r₁ ∧ g • q₂ = r₂)) ∧
    ((Gp = ⊤ ∧ (κ = .Tits ∨ κ = .G2d)) → ∀ u v : ι.Γ, ι.graph.dist u v = κ.m →
      (CosetGeom.vtype u = true →
        IsComplementIn (stv ι u ⊓ stv ι v) (Qu p Gp ι u) (stv ι u)) ∧
      (CosetGeom.vtype u = false →
        Nonempty (↥(stv ι u ⊓ stv ι v) ≃* DihedralGroup 5) ∨
          Nonempty (↥(stv ι u ⊓ stv ι v) ≃* Multiplicative (ZMod 3))))

@[expose] def F_4_6 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
    ∀ ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂), ι = incl M₁ M₂ →
    (∀ a : β.Γ,
      (IsLieExtAmalgam M₁ M₂ → β.PathTrans a (κ.m + 1)) ∧
      ((Gp = ⊤ ∧ (κ = .G2d ∨ κ = .Tits)) →
        (CosetGeom.vtype a = false → β.PathTrans a κ.m) ∧
        (CosetGeom.vtype a = true →
          β.PathTrans a (κ.m - 1) ∧
          (∃ q₁ ∈ GPath.nbPaths β.graph a κ.m, ∃ q₂ ∈ GPath.nbPaths β.graph a κ.m,
            GPath.nbPaths β.graph a κ.m = pathOrbit (stv β a) q₁ ∪ pathOrbit (stv β a) q₂ ∧
            Disjoint (pathOrbit (stv β a) q₁) (pathOrbit (stv β a) q₂) ∧
            Nat.card ↥(pathOrbit (stv β a) q₁) = Nat.card ↥(pathOrbit (stv β a) q₂)) ∧
          ∀ q₁ ∈ GPath.nbPaths β.graph a κ.m, ∀ q₂ ∈ GPath.nbPaths β.graph a κ.m, q₁ κ.m = q₂ κ.m →
            ∃ g ∈ stv β a ⊓ stv β (q₁ κ.m), g • q₁ = q₂))) ∧
    (∃ r : PermQuasiEquiv ↥(stv ι ι.xv) (PathSet ι.graph ι.xv) ↥(stv β β.xv) (PathSet β.graph β.xv),
        (∀ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1,
          ((r.grp ⟨f1 (c := ι) a, MulAction.mem_stabilizer_iff.mpr (f1_smul_xv a)⟩ : ↥(stv β β.xv)) :
            β.G0) = f1 (c := β) a) ∧
        ∀ pp : PathSet ι.graph ι.xv, (r.set pp).1 = pp.1 ∧ (pp.NoBack ↔ (r.set pp).NoBack)) ∧
    (∃ r : PermQuasiEquiv ↥(stv ι ι.lv) (PathSet ι.graph ι.lv) ↥(stv β β.lv) (PathSet β.graph β.lv),
        (∀ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2,
          ((r.grp ⟨f2 (c := ι) a, MulAction.mem_stabilizer_iff.mpr (f2_smul_lv a)⟩ : ↥(stv β β.lv)) :
            β.G0) = f2 (c := β) a) ∧
        ∀ pp : PathSet ι.graph ι.lv, (r.set pp).1 = pp.1 ∧ (pp.NoBack ↔ (r.set pp).NoBack)) ∧
    (∀ n : ℕ, n ≤ κ.m → ∀ a : β.Γ, ∀ q : GPath β.graph n, q ∈ GPath.nbPaths β.graph a n →
      (0 < n → ¬ ((Gp = ⊤ ∧ (κ = .G2d ∨ κ = .Tits)) ∧ CosetGeom.vtype a = true ∧ n = κ.m) →
        (∀ j : ℕ, n = 2 * j + 1 → (q.stabPath : Subgroup β.G0).relIndex (stv β a) =
          (qOfType (RankTwoAmalgam.ofSubgroups M₁ M₂) (CosetGeom.vtype a) + 1) *
            ((RankTwoAmalgam.ofSubgroups M₁ M₂).qOne * (RankTwoAmalgam.ofSubgroups M₁ M₂).qTwo) ^ j) ∧
        (∀ j : ℕ, n = 2 * j + 2 → (q.stabPath : Subgroup β.G0).relIndex (stv β a) =
          (qOfType (RankTwoAmalgam.ofSubgroups M₁ M₂) (CosetGeom.vtype a) + 1) *
            ((RankTwoAmalgam.ofSubgroups M₁ M₂).qOne * (RankTwoAmalgam.ofSubgroups M₁ M₂).qTwo) ^ j *
            qOfType (RankTwoAmalgam.ofSubgroups M₁ M₂) (!CosetGeom.vtype a))) ∧
      (n < κ.m →
        (∀ u ∈ CosetGeom.sphere n a, ∀ v ∈ CosetGeom.sphere n a, ∃ g ∈ stv β a, g • u = v) ∧
        q n ∈ CosetGeom.sphere n a ∧ q.IsGeodesic ∧
        (∀ r : GPath β.graph n, r 0 = a → r n = q n → r.IsGeodesic → r = q) ∧
        (2 ≤ n → ∀ S : Set β.Γ, ¬ IsPolygon β.graph S (2 * n)) ∧
        Nat.card ↥(CosetGeom.sphere n a) = (q.stabPath : Subgroup β.G0).relIndex (stv β a))) ∧
    (∀ a : β.Γ, ∀ q : GPath β.graph κ.m, q ∈ GPath.nbPaths β.graph a κ.m →
      (IsComplementIn (q.stabPath : Subgroup β.G0) (Qu p Gp β (q κ.m))
          (stv β (q (κ.m - 1)) ⊓ stv β (q κ.m)) ∨
        ((Gp = ⊤ ∧ (κ = .G2d ∨ κ = .Tits)) ∧ CosetGeom.vtype a = false ∧
          (q.stabPath : Subgroup β.G0) ⊓ Qu p Gp β (q κ.m) = ⊥ ∧
          (Qu p Gp β (q κ.m) ⊔ (q.stabPath : Subgroup β.G0)).relIndex
            (stv β (q (κ.m - 1)) ⊓ stv β (q κ.m)) = 2)) ∧
      (q κ.m ∈ CosetGeom.sphere κ.m a ∧
        (∀ r ∈ GPath.nbPaths β.graph a κ.m, r.IsGeodesic ∧ r κ.m ∈ CosetGeom.sphere κ.m a) ∧
        ((∀ r : GPath β.graph κ.m, r 0 = a → r κ.m = q κ.m → r.IsGeodesic → r = q) ∨
          (IsComplementIn (stv β a ⊓ stv β (q κ.m)) (Qu p Gp β a) (stv β a) ∧
            (∀ q₁ ∈ β.geods κ.m a (q κ.m), ∀ q₂ ∈ β.geods κ.m a (q κ.m), q₁ ≠ q₂ →
              ∀ r₁ ∈ β.geods κ.m a (q κ.m), ∀ r₂ ∈ β.geods κ.m a (q κ.m), r₁ ≠ r₂ →
                ∃ g ∈ stv β a ⊓ stv β (q κ.m), g • q₁ = r₁ ∧ g • q₂ = r₂) ∧
            Nat.card ↥(β.geods κ.m a (q κ.m)) =
              qOfType (RankTwoAmalgam.ofSubgroups M₁ M₂) (CosetGeom.vtype a) + 1 ∧
            Set.BijOn (fun r : GPath β.graph κ.m => r 1) (β.geods κ.m a (q κ.m))
              (CosetGeom.nbrs a)) ∨
          ((Gp = ⊤ ∧ κ = .Tits) ∧ CosetGeom.vtype a = false ∧
            Nonempty (↥(stv β a ⊓ stv β (q κ.m)) ≃* DihedralGroup 5) ∧
            (∀ q₁ ∈ β.geods κ.m a (q κ.m), ∀ q₂ ∈ β.geods κ.m a (q κ.m),
              ∃ g ∈ stv β a ⊓ stv β (q κ.m), g • q₁ = q₂) ∧
            Nat.card ↥(β.geods κ.m a (q κ.m)) = 5 ∧
            Set.BijOn (fun r : GPath β.graph κ.m => r 1) (β.geods κ.m a (q κ.m))
              (CosetGeom.nbrs a)) ∨
          ((Gp = ⊤ ∧ κ = .G2d) ∧ CosetGeom.vtype a = false ∧
            Nonempty (↥(stv β a ⊓ stv β (q κ.m)) ≃* Multiplicative (ZMod 3)) ∧
            (∀ q₁ ∈ β.geods κ.m a (q κ.m), ∀ q₂ ∈ β.geods κ.m a (q κ.m),
              ∃ g ∈ stv β a ⊓ stv β (q κ.m), g • q₁ = q₂) ∧
            Nat.card ↥(β.geods κ.m a (q κ.m)) = 3 ∧
            Set.BijOn (fun r : GPath β.graph κ.m => r 1) (β.geods κ.m a (q κ.m))
              (CosetGeom.nbrs a)))))

end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def pointwiseStab {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z)
    (S : Set c.Γ) : Subgroup c.G0 :=
  ⨅ v ∈ S, stv c v

open scoped Pointwise in
@[expose] def setStab {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z)
    (S : Set c.Γ) : Subgroup c.G0 :=
  MulAction.stabilizer c.G0 S

@[expose] def IsReflectionOn {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z)
    (s : c.G0) (S : Set c.Γ) (u : c.Γ) : Prop :=
  (∀ w ∈ S, (s * s) • w = w) ∧ s ∈ setStab c S ∧ s • u = u ∧
    Set.ncard {w : c.Γ | w ∈ S ∧ s • w = w} = 2

@[expose] def F48Concl (κ : GLKind) (p f : ℕ) {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) : Prop :=
  (∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
    ∃ (Ġ : Type) (_ : Group Ġ) (β' : Cpl M₁ M₂ Ġ),
      Amalgam.Completion.IsEquivalent β.toCompletion β'.toCompletion ∧ IsLieExtGroup β'.G0 κ p f ∧
      Nonempty (β.G0 ≃* β'.G0)) ∧
  (Gp = ⊤ →
    (∃ (Y₀ : Type) (_ : Group Y₀) (β₀ : Cpl M₁ M₂ Y₀), β₀.IsFaithful ∧ β₀.IsSmall κ.m ∧
      ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
        Amalgam.Completion.IsQuasiEquivalent β.toCompletion β₀.toCompletion) ∧
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m → Nonempty (β.G0 ≃* E))

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def F_4_8 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → F48Concl κ p f Gp M₁ M₂

@[expose] def F_4_9 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 GLKind.L3 2 1 Gp M₁ M₂ → Gp = ⊤ →
    (∃ tau : Amalgam.Aut (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam,
      tau ≠ 1 ∧ tau * tau = 1 ∧
      (∀ pointElement : ↥M₁, tau.1 .one pointElement = pointElement) ∧
      (∃ centralInvolution ∈ CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂) ⊓
          Subgroup.centralizer ((CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂) : Subgroup E) : Set E),
        centralInvolution ≠ 1 ∧ centralInvolution * centralInvolution = 1 ∧
        ∀ lineElement : ↥M₂, M₂.subtype (tau.1 .two lineElement) =
          centralInvolution * (lineElement : E) * centralInvolution⁻¹) ∧
      ∃ autEquiv : (↥(CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂)) × Multiplicative (ZMod 2)) ≃*
          Amalgam.Aut (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam,
        autEquiv (1, Multiplicative.ofAdd (1 : ZMod 2)) = tau ∧
        (∀ sylowElement : ↥(CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂)), ∀ pointElement : ↥M₁,
          M₁.subtype ((autEquiv (sylowElement, 1)).1 .one pointElement) =
            (sylowElement : E) * (pointElement : E) * (sylowElement : E)⁻¹) ∧
        (∀ sylowElement : ↥(CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂)), ∀ lineElement : ↥M₂,
          M₂.subtype ((autEquiv (sylowElement, 1)).1 .two lineElement) =
            (sylowElement : E) * (lineElement : E) * (sylowElement : E)⁻¹)) ∧
    ∃ (Y₁ Y₂ : Type) (_ : Group Y₁) (_ : Group Y₂) (β₁ : Cpl M₁ M₂ Y₁) (β₂ : Cpl M₁ M₂ Y₂),
      β₁.IsFaithful ∧ β₂.IsFaithful ∧ β₁.IsSmall 3 ∧ β₂.IsSmall 3 ∧
      ¬ Amalgam.Completion.IsEquivalent β₁.toCompletion β₂.toCompletion ∧
      ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall 3 →
        Amalgam.Completion.IsEquivalent β.toCompletion β₁.toCompletion ∨
          Amalgam.Completion.IsEquivalent β.toCompletion β₂.toCompletion


@[expose] def F_4_11 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ →
    ∀ ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂), ι = incl M₁ M₂ →
    (∀ (Ġ : Type) [Group Ġ] (μ : Cpl M₁ M₂ Ġ), μ.IsFaithful →
      (Amalgam.Completion.IsQuasiEquivalent μ.toCompletion ι.toCompletion ↔ Nonempty (E ≃* μ.G0))) ∧
    ∀ hι : ι.toCompletion.IsFaithful,
      Nat.card ↥{K : Subgroup (Amalgam.gp (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam) |
          ∃ a : Amalgam.Aut (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam,
            K = ((Amalgam.Completion.act a ι.toCompletion).hat).ker} =
        ((Amalgam.Completion.sigma ι.toCompletion hι).range).index

@[expose] def F_4_12 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
      ∀ a b : β.Γ, b ∈ CosetGeom.sphere κ.m a →
        ∃ q₁ ∈ β.geods κ.m a b, ∃ q₂ ∈ β.geods κ.m a b, q₁ ≠ q₂

@[expose] def F_4_13 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
      IsGenPolygon β.graph κ.m ∧ Nat.card β.G0 = Nat.card E

@[expose] def F_4_14 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
      (∀ a b : β.Γ, b ∈ CosetGeom.sphere κ.m a →
        (∀ S : Set β.Γ, (a ∈ S ∧ b ∈ S ∧ β.IsApartment κ.m S) ↔
          ∃ q₁ ∈ β.geods κ.m a b, ∃ q₂ ∈ β.geods κ.m a b, q₁ ≠ q₂ ∧
            S = pathVerts q₁ ∪ pathVerts q₂) ∧
        (∀ c ∈ CosetGeom.nbrs a, ∃! q : GPath β.graph κ.m, q ∈ β.geods κ.m a b ∧ q 1 = c) ∧
        Nat.card ↥{S : Set β.Γ | a ∈ S ∧ b ∈ S ∧ β.IsApartment κ.m S} =
          Nat.choose (qOfType (RankTwoAmalgam.ofSubgroups M₁ M₂) (CosetGeom.vtype a) + 1) 2) ∧
      (∀ s t : Set β.Γ, IsSimplex β.graph s → IsSimplex β.graph t →
        ∃ S : Set β.Γ, β.IsApartment κ.m S ∧ s ⊆ S ∧ t ⊆ S)

end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def IsF415W {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z) (m : ℕ)
    (S : Set c.Γ) (sx sl : c.G0) : Prop :=
  sx ∈ stv c c.xv ∧ sl ∈ stv c c.lv ∧ IsReflectionOn c sx S c.xv ∧ IsReflectionOn c sl S c.lv ∧
  Nat.card (↥(Subgroup.closure {sx, sl}) ⧸
      (pointwiseStab c S).subgroupOf (Subgroup.closure {sx, sl})) = 2 * m ∧
  ∀ u ∈ S, ∀ v ∈ S, CosetGeom.vtype u = CosetGeom.vtype v →
    ∃ w ∈ Subgroup.closure {sx, sl}, w • u = v

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def F_4_15 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
    (¬ (Gp = ⊤ ∧ κ = .Tits) → ∀ S₁ S₂ : Set β.Γ, β.IsApartment κ.m S₁ → β.IsApartment κ.m S₂ →
      ∃ g : β.G0, (fun w => g • w) '' S₁ = S₂) ∧
    (¬ (Gp = ⊤ ∧ κ = .G2d) → ∀ S : Set β.Γ, β.IsApartment κ.m S → β.xv ∈ S → β.lv ∈ S →
      ∃ sx sl : β.G0, IsF415W β κ.m S sx sl ∧
        ((Gp = ⊤ ∧ κ = .Tits) → ∀ w ∈ Subgroup.closure {sx, sl}, (∀ v ∈ S, w • v = v) → w = 1)) ∧
    ((Gp = ⊤ ∧ κ = .Tits) → ∃ S₁ S₂ : Set β.Γ, β.IsApartment κ.m S₁ ∧ β.IsApartment κ.m S₂ ∧
      (∀ S : Set β.Γ, β.IsApartment κ.m S →
        (∃ g : β.G0, (fun w => g • w) '' S₁ = S) ∨ (∃ g : β.G0, (fun w => g • w) '' S₂ = S)) ∧
      (¬ ∃ g : β.G0, (fun w => g • w) '' S₁ = S₂) ∧
      Nat.card ↥{S : Set β.Γ | ∃ g : β.G0, (fun w => g • w) '' S₁ = S} =
        Nat.card ↥{S : Set β.Γ | ∃ g : β.G0, (fun w => g • w) '' S₂ = S}) ∧
    ((Gp = ⊤ ∧ κ = .G2d) → ∀ S : Set β.Γ, β.IsApartment κ.m S → β.xv ∈ S → β.lv ∈ S →
      ∀ c ∈ CosetGeom.nbrs β.xv, c ∈ S → c ≠ β.lv →
        ∃ sl sc : β.G0, sl ∈ stv β β.lv ∧ sc ∈ stv β c ∧ IsReflectionOn β sl S β.lv ∧
          IsReflectionOn β sc S c ∧ setStab β S = Subgroup.closure {sl, sc} ∧
          Nonempty (↥(setStab β S) ≃* Equiv.Perm (Fin 3)) ∧
          Set.ncard {u : β.Γ | u ∈ S ∧ CosetGeom.vtype u = false} = 6 ∧
          (∀ u ∈ S, CosetGeom.vtype u = false → ∀ v ∈ S, CosetGeom.vtype v = false →
            ∃! w : ↥(setStab β S), (w : β.G0) • u = v) ∧
          {u : β.Γ | u ∈ S ∧ CosetGeom.vtype u = true} =
            {u | ∃ w ∈ setStab β S, w • β.lv = u} ∪ {u | ∃ w ∈ setStab β S, w • c = u} ∧
          Disjoint {u : β.Γ | ∃ w ∈ setStab β S, w • β.lv = u} {u | ∃ w ∈ setStab β S, w • c = u} ∧
          Set.ncard {u : β.Γ | ∃ w ∈ setStab β S, w • β.lv = u} = 3 ∧
          Set.ncard {u : β.Γ | ∃ w ∈ setStab β S, w • c = u} = 3)

@[expose] def F_4_16 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → IsLieExtAmalgam M₁ M₂ →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
      ∀ S : Set β.Γ, β.IsApartment κ.m S → β.xv ∈ S → β.lv ∈ S →
        (Sp p Gp β ≤ stv β β.xv ⊓ stv β β.lv ∧
          ((Sp p Gp β).subgroupOf (stv β β.xv ⊓ stv β β.lv)).Normal ∧
          IsComplementIn (setStab β S ⊓ pointwiseStab β S) (Sp p Gp β) (stv β β.xv ⊓ stv β β.lv)) ∧
        ∀ sx sl : β.G0, IsF415W β κ.m S sx sl →
          setStab β S = (setStab β S ⊓ pointwiseStab β S) ⊔ Subgroup.closure {sx, sl}

@[expose] def F_4_17 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → IsLieExtAmalgam M₁ M₂ → F48Concl κ p f Gp M₁ M₂

@[expose] def F_4_24 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → Finite β.G0 → Nat.card β.G0 ≤ Nat.card E →
      Nat.card β.G0 = Nat.card E ∧ ∃ (Ġ : Type) (_ : Group Ġ),
        IsLieExtGroup Ġ κ p f ∧ Nonempty (β.G0 ≃* Ġ)

@[expose] def F_4_26 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
      ∀ s₁ s₂ : β.G0, s₁ * s₁ = 1 → s₂ * s₂ = 1 →
        s₁ ∈ stv β β.xv → s₁ ∉ stv β β.xv ⊓ stv β β.lv →
        s₂ ∈ stv β β.lv → s₂ ∉ stv β β.xv ⊓ stv β β.lv →
          (∀ n : ℕ, 0 < n → n < κ.m → (s₁ * s₂) ^ n ≠ 1) ∧
          (orderOf (s₁ * s₂) = κ.m →
            ∃ (Ġ : Type) (_ : Group Ġ), IsLieExtGroup Ġ κ p f ∧ Nonempty (β.G0 ≃* Ġ))

end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section F418

variable {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z)

@[expose] def HasCycle (s : c.G0) (a b : c.Γ) : Prop := s * s = 1 ∧ a ≠ b ∧ s • a = b ∧ s • b = a

@[expose] def N1set (κ : GLKind) (cc y : c.Γ) : Set c.G0 :=
  if κ = GLKind.Tits then
    {s | s ∈ stv c c.xv ∧ HasCycle c s c.lv cc ∧
      ∃ q : GPath c.graph κ.m, q 0 = c.xv ∧ q.IsGeodesic ∧
        (q.stabPath : Subgroup c.G0) = Subgroup.zpowers s}
  else {s | s ∈ stv c c.lv ∧ HasCycle c s c.xv y}

@[expose] def N2set (κ : GLKind) (cc y y' : c.Γ) : Set c.G0 :=
  if κ = GLKind.Tits then {t | t ∈ stv c c.lv ∧ HasCycle c t c.xv y}
  else {t | t ∈ stv c cc ∧ HasCycle c t c.xv y'}

@[expose] def m0Of (κ : GLKind) : ℕ := if κ = GLKind.Tits then 8 else 3

@[expose] def SigmaST (κ : GLKind) (cc : c.Γ) (s t : c.G0) : Set c.Γ :=
  {u | ∃ w ∈ Subgroup.closure {s, t}, w • c.xv = u} ∪ {u | ∃ w ∈ Subgroup.closure {s, t}, w • c.lv = u} ∪
    (if κ = GLKind.G2d then {u | ∃ w ∈ Subgroup.closure {s, t}, w • cc = u} else ∅)

@[expose] def Pset (κ : GLKind) (cc y y' : c.Γ) : Set (c.G0 × c.G0) :=
  {st | st.1 ∈ N1set c κ cc y ∧ st.2 ∈ N2set c κ cc y y' ∧ orderOf (st.1 * st.2) = m0Of κ}

@[expose] def Bset (κ : GLKind) (cc y y' : c.Γ) : Set (Set c.Γ) :=
  {S | c.IsApartment κ.m S ∧
    (if κ = GLKind.Tits then ({cc, c.xv, c.lv, y} : Set c.Γ) ⊆ S
      else ({y', cc, c.xv, c.lv, y} : Set c.Γ) ⊆ S)}

end F418

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def F_4_19 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → Gp = ⊤ → (κ = .G2d ∨ κ = .Tits) →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
      ∀ cc ∈ CosetGeom.nbrs β.xv, cc ≠ β.lv →
      ∀ y ∈ CosetGeom.nbrs β.lv, y ≠ β.xv →
      ∀ y' ∈ CosetGeom.nbrs cc, y' ≠ β.xv →
        Set.BijOn (fun st : β.G0 × β.G0 => SigmaST β κ cc st.1 st.2) (Pset β κ cc y y')
          (Bset β κ cc y y')

@[expose] def F_4_20 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → Gp = ⊤ → (κ = .G2d ∨ κ = .Tits) →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
      ∀ cc ∈ CosetGeom.nbrs β.xv, cc ≠ β.lv →
      ∀ y ∈ CosetGeom.nbrs β.lv, y ≠ β.xv →
      ∀ y' ∈ CosetGeom.nbrs cc, y' ≠ β.xv →
        (κ = .Tits →
          Set.ncard (N1set β κ cc y) = 2 ^ 4 ∧ Set.ncard (N2set β κ cc y y') = 2 ^ 6 ∧
          Set.ncard (Pset β κ cc y y') = 2 ^ 9 ∧
          ∀ s ∈ N1set β κ cc y, ∀ s' ∈ N1set β κ cc y,
            ∃ g ∈ Qu p Gp β β.xv ⊓ Qu p Gp β β.lv, g * s * g⁻¹ = s') ∧
        (κ = .G2d →
          Set.ncard (N1set β κ cc y) = 4 ∧ Set.ncard (N2set β κ cc y y') = 4 ∧
          Set.ncard (Pset β κ cc y y') = 8 ∧
          ∀ s ∈ N1set β κ cc y, ∀ s' ∈ N1set β κ cc y,
            ∃ g ∈ Qu p Gp β β.lv ⊓ Qu p Gp β cc, g * s * g⁻¹ = s')

@[expose] def F_4_21 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → Gp = ⊤ → (κ = .G2d ∨ κ = .Tits) →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
    ∀ (Y' : Type) [Group Y'] (ρ : Cpl M₁ M₂ Y'), ρ.IsFaithful →
      ∀ cc ∈ CosetGeom.nbrs β.xv, cc ≠ β.lv →
      ∀ cc' ∈ CosetGeom.nbrs ρ.xv, cc' ≠ ρ.lv →
        (∀ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1,
          f1 (c := β) a ∈ stv β cc ↔ f1 (c := ρ) a ∈ stv ρ cc') →
        ∃ ρ₃ : ↥(stv β cc) ≃* ↥(stv ρ cc'),
          (∀ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1, ∀ h : f1 (c := β) a ∈ stv β cc,
            ((ρ₃ ⟨f1 (c := β) a, h⟩ : ↥(stv ρ cc')) : ρ.G0) = f1 (c := ρ) a) ∧
          (∀ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2, ∀ h : f2 (c := β) a ∈ stv β cc,
            ((ρ₃ ⟨f2 (c := β) a, h⟩ : ↥(stv ρ cc')) : ρ.G0) = f2 (c := ρ) a)

@[expose] def F_4_22 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → Gp = ⊤ → (κ = .G2d ∨ κ = .Tits) →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
      Subgroup.center β.G0 = ⊥

end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def ctr {E : Type} [Group E] (K : Subgroup E) : Subgroup E :=
  K ⊓ Subgroup.centralizer (K : Set E)

@[expose] def cj {E : Type} [Group E] (g : E) (X : Subgroup E) : Subgroup E :=
  X.map (MulAut.conj g).toMonoidHom

@[expose] def InvClasses (E : Type) [Group E] : Set (ConjClasses E) :=
  {C | ∃ x ∈ C.carrier, x ≠ 1 ∧ x * x = 1}

@[expose] def ClassMeetsCenter {E : Type} [Group E] (S : Subgroup E) (C : ConjClasses E) : Prop :=
  ∃ z ∈ C.carrier, z ∈ ctr S


@[expose] def IsShortRootInv {E : Type} [Group E] (κ : GLKind)
    (Gp M₁ M₂ : Subgroup E) (element : E) : Prop :=
  ∃ degree : ℕ, ∃ chart : NativeChart κ 2 degree Gp,
    chart.Matches M₁ M₂ ∧ chart.RootInvolution true element

@[expose] def bmap {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) :
    ↥(M₁ ⊓ M₂) →* β.G0 :=
  (f1 (c := β)).comp (RankTwoAmalgam.ofSubgroups M₁ M₂).α1

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


@[expose] def F_4_27 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E)
    (hyp : HypF_4_4 κ 2 f Gp M₁ M₂), Gp = ⊤ →
    let chart := hyp.toHypF_4_4g.chart
    chart.Matches M₁ M₂ ∧
    ((κ = .L3 ∨ κ = .G2d) → Set.ncard (InvClasses E) = 1 ∧
      ∀ element : E, element ≠ 1 → element * element = 1 →
        chart.RootInvolution false element) ∧
    (∀ kind : κ = .Sp4, Set.ncard (InvClasses E) = 3 ∧
      (∀ C ∈ InvClasses E, ClassMeetsCenter (pCoreOf 2 (M₁ ⊓ M₂)) C) ∧
      ∃ long short mixed : E,
        chart.RootInvolution false long ∧ chart.RootInvolution true short ∧
        mixed ∈ Gp ∧ mixed ≠ 1 ∧ mixed * mixed = 1 ∧
        (∃ conjugator ∈ Gp, ∃ a ∈ chart.longRoot, ∃ b ∈ chart.shortRoot,
          a ≠ 1 ∧ b ≠ 1 ∧ conjugator * mixed * conjugator⁻¹ = a * b) ∧
        ¬ IsConj long short ∧ ¬ IsConj long mixed ∧ ¬ IsConj short mixed ∧
        (∀ element : E, element ≠ 1 → element * element = 1 →
          IsConj element long ∨ IsConj element short ∨ IsConj element mixed) ∧
        (∀ element : E, chart.RootInvolution false element ↔ IsConj element long) ∧
        (∀ element : E, chart.RootInvolution true element ↔ IsConj element short) ∧
        (∀ element : E, (kind ▸ chart).C2Involution element ↔ IsConj element mixed)) ∧
    ((κ ≠ .L3 ∧ κ ≠ .Sp4 ∧ κ ≠ .G2d) →
      Set.ncard (InvClasses E) = 2 ∧
      (∃! C : ConjClasses E, C ∈ InvClasses E ∧
        ClassMeetsCenter (pCoreOf 2 (M₁ ⊓ M₂)) C) ∧
      (∀ element : E, element ≠ 1 → element * element = 1 →
        chart.RootInvolution false element ∨ chart.RootInvolution true element) ∧
      (∀ element : E, element ≠ 1 → element * element = 1 →
        (chart.RootInvolution false element ↔
          ∃ conjugator ∈ Gp, conjugator * element * conjugator⁻¹ ∈
            ctr (pCoreOf 2 (M₁ ⊓ M₂)))) ∧
      (∀ element : E, ¬ (chart.RootInvolution false element ∧
        chart.RootInvolution true element))) ∧
    (κ ≠ .L3 →
      (∀ element ∈ ctr (oPPrime 2 M₁), element ≠ 1 →
        (κ ≠ .G2d → chart.RootInvolution false element) ∧
        (κ = .G2d → element * element = 1 → chart.RootInvolution false element) ∧
        Subgroup.centralizer ({element} : Set E) ≤ M₁ ∧
        oPPrime 2 M₁ = oPPrime 2 (Subgroup.centralizer ({element} : Set E)) ∧
        ((κ ≠ .U4 ∧ κ ≠ .U5) →
          oPPrime 2 M₁ = Subgroup.centralizer ({element} : Set E))) ∧
      (κ ≠ .G2d → ∃ element ∈ pCoreOf 2 M₂,
        chart.RootInvolution true element ∧
        Subgroup.centralizer ({element} : Set E) ≤ M₂)) ∧
    (κ = .L3 → ∀ element ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂)), element ≠ 1 →
      pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Subgroup.centralizer ({element} : Set E)))

@[expose] def F_4_30 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ 2 f Gp M₁ M₂ →
    ∀ T : Subgroup E, IsSylowOf 2 T (M₁ ⊓ M₂) →
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
    ∀ U U' : Set ↥(M₁ ⊓ M₂), (∀ u ∈ U, (u : E) ∈ T) → (∀ u ∈ U', (u : E) ∈ T) →
      (∃ g : E, (fun u : E => g * u * g⁻¹) '' (Subtype.val '' U) = Subtype.val '' U') →
      ∃ h : β.G0, (fun w : β.G0 => h * w * h⁻¹) '' (bmap β '' U) = bmap β '' U'

end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section F431World

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

@[expose] noncomputable def epsG (β : Cpl M₁ M₂ Y) (ε : Y →* M) : β.G0 →* M :=
  ε.comp ((β.φ1.range ⊔ β.φ2.range).subtype)

@[expose] noncomputable def MiOne (β : Cpl M₁ M₂ Y) (ε : Y →* M) : Subgroup M :=
  (f1 (c := β)).range.map (epsG β ε)

@[expose] noncomputable def MiTwo (β : Cpl M₁ M₂ Y) (ε : Y →* M) : Subgroup M :=
  (f2 (c := β)).range.map (epsG β ε)

@[expose] noncomputable def GiOne (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) : Subgroup M :=
  (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β))).map (epsG β ε)

@[expose] noncomputable def GiTwo (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) : Subgroup M :=
  (((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β))).map (epsG β ε)

@[expose] noncomputable def SinM (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) : Subgroup M :=
  (Sp 2 Gp β).map (epsG β ε)

@[expose] noncomputable def bM (β : Cpl M₁ M₂ Y) (ε : Y →* M) : ↥(M₁ ⊓ M₂) →* M :=
  (epsG β ε).comp (bmap β)

@[expose] noncomputable def imB (β : Cpl M₁ M₂ Y) (ε : Y →* M) (K : Subgroup E) : Subgroup M :=
  (K.subgroupOf (M₁ ⊓ M₂)).map (bM β ε)

end F431World

@[expose] def IsTISet {M : Type} [Group M] (Z : Subgroup M) : Prop :=
  ∀ g : M, cj g Z = Z ∨ Z ⊓ cj g Z = ⊥

@[expose] def IsL43 (M : Type) [Group M] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 3 ∧
    Nonempty (M ≃* StatedProj (StatedSL 4 K))

@[expose] def FstarEqO2 {M : Type} [Group M] (H : Subgroup M) : Prop :=
  (CFSG.generalizedFitting ↥H).map H.subtype = pCoreOf 2 H

structure HypF_4_31 (κ : GLKind) (f : ℕ) {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) {M : Type} [Group M] (ε : Y →* M) (z : M) : Prop where
  amalgam : HypF_4_4 κ 2 f Gp M₁ M₂
  not_G2d : κ ≠ GLKind.G2d
  not_L32 : ¬ (κ = GLKind.L3 ∧ f = 1)
  faithful : β.IsFaithful
  finite_M : Finite M
  inj : Function.Injective (epsG β ε)
  z_inv : z ≠ 1 ∧ z * z = 1
  z_mem : (κ ≠ GLKind.L3 → z ∈ ctr (oPPrime 2 (GiOne Gp β ε))) ∧
    (κ = GLKind.L3 → z ∈ ctr (SinM Gp β ε))
  ha : (κ = GLKind.Sp4 ∨ κ = GLKind.U4 ∨ κ = GLKind.U5) →
    Subgroup.normalizer ((ctr (pCoreOf 2 (GiOne Gp β ε)) : Subgroup M) : Set M) = MiOne β ε ∧
    Subgroup.normalizer ((ctr (pCoreOf 2 (GiTwo Gp β ε)) : Subgroup M) : Set M) = MiTwo β ε
  hb : Subgroup.centralizer ({z} : Set M) ≤ MiOne β ε
  hc : κ = GLKind.Sp4 →
    (∀ t ∈ ctr (oPPrime 2 (GiTwo Gp β ε)), t ≠ 1 → Subgroup.centralizer ({t} : Set M) ≤ MiTwo β ε) ∧
    ∀ u ∈ ctr (SinM Gp β ε), u ≠ 1 → u * u = 1 → FstarEqO2 (Subgroup.centralizer ({u} : Set M))
  hd : κ = GLKind.Sp4 → Odd (MiOne β ε ⊓ MiTwo β ε).index
  he : oTwoRes (⊤ : Subgroup M) = ⊤ ∨ (f = 1 ∧ (κ = GLKind.Sp4 ∨ κ = GLKind.G2 ∨ κ = GLKind.F4tw))

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def F_4_33 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z →
    ∀ T : Subgroup M, IsSylowOf 2 T (MiOne β ε ⊓ MiTwo β ε) → IsSylowOf 2 T ⊤

@[expose] def F_4_34 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z →
    (κ ≠ .L3 → IsTISet (ctr (oPPrime 2 (GiOne Gp β ε))) ∧
      MiOne β ε = Subgroup.normalizer ((ctr (oPPrime 2 (GiOne Gp β ε)) : Subgroup M) : Set M)) ∧
    (κ = .Sp4 → IsTISet (ctr (oPPrime 2 (GiTwo Gp β ε))) ∧
      MiTwo β ε = Subgroup.normalizer ((ctr (oPPrime 2 (GiTwo Gp β ε)) : Subgroup M) : Set M)) ∧
    (κ = .L3 → IsTISet (ctr (SinM Gp β ε)) ∧
      MiOne β ε ⊓ MiTwo β ε = Subgroup.normalizer ((ctr (SinM Gp β ε) : Subgroup M) : Set M))


@[expose] def F_4_35 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z →
    ∀ i j : ↥(M₁ ⊓ M₂), (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      i ≠ 1 → j ≠ 1 → i * i = 1 → j * j = 1 →
      ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j))

@[expose] def F_4_38 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M →
    ∀ T : Subgroup M, IsSylowOf 2 T (MiOne β ε ⊓ MiTwo β ε) →
      T = SinM Gp β ε ∧ oPPrime 2 (⊤ : Subgroup E) = Gp ∧ Odd Gp.index


@[expose] def F_4_39 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → κ = .Sp4 →
    ∀ u : ↥(M₁ ⊓ M₂), (u : E) ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → u ≠ 1 → u * u = 1 →
      (u : E) ∉ ctr (oPPrime 2 (Gp ⊓ M₁)) → (u : E) ∉ ctr (oPPrime 2 (Gp ⊓ M₂)) →
      Subgroup.centralizer ({bM β ε u} : Set M) ≤ MiOne β ε ⊓ MiTwo β ε

@[expose] def F_4_40 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M →
    ∀ v : ↥(M₁ ⊓ M₂), (v : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → v ≠ 1 → v * v = 1 →
      IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(v : E)} : Set E))
        (Gp ⊓ Subgroup.centralizer ({(v : E)} : Set E)) →
      IsSylowOf 2 (SinM Gp β ε ⊓ Subgroup.centralizer ({bM β ε v} : Set M))
        (Subgroup.centralizer ({bM β ε v} : Set M))


@[expose] def F_4_42 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → κ ≠ .L3 →
      ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv κ Gp M₁ M₂ (t : E) ∧
        Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε


@[expose] def F_4_43 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → κ ≠ .L3 → Nat.card M = Nat.card E


@[expose] def F_4_44_partial : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → κ ≠ .L3 →
      ∃ (Ġ : Type) (_ : Group Ġ) (Gq : Subgroup Ġ), IsLieExtBy Ġ Gq κ 2 f ∧ Odd Gq.index ∧
        Nonempty (M ≃* Ġ)

@[expose] def F_4_45 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → κ = .L3 → (epsG β ε).range = ⊤


@[expose] def F_4_46 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → κ = .L3 →
    ∀ T : Subgroup M, IsSylowOf 2 T (MiOne β ε ⊓ MiTwo β ε) →
      (∀ j : M, j ≠ 1 → j * j = 1 → IsConj z j) ∧
      (∀ j : M, j ≠ 1 → j * j = 1 →
        oPPrime 2 (Subgroup.centralizer ({j} : Set M)) = pCoreOf 2 (Subgroup.centralizer ({j} : Set M)) ∧
        IsSylowOf 2 (pCoreOf 2 (Subgroup.centralizer ({j} : Set M))) ⊤) ∧
      ((∀ g : M, cj g (pCoreOf 2 (oPPrime 2 (GiOne Gp β ε))) ≤ MiOne β ε →
          cj g (pCoreOf 2 (oPPrime 2 (GiOne Gp β ε))) = pCoreOf 2 (oPPrime 2 (GiOne Gp β ε))) ∧
        (∀ g : M, cj g (pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε))) ≤ MiTwo β ε →
          cj g (pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε))) = pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε)))) ∧
      (MiOne β ε = Subgroup.normalizer ((pCoreOf 2 (oPPrime 2 (GiOne Gp β ε)) : Subgroup M) : Set M) ∧
        MiTwo β ε = Subgroup.normalizer ((pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε)) : Subgroup M) : Set M) ∧
        ({W : Subgroup M | (∃ g : M, W = cj g (ctr T)) ∧ W ≤ pCoreOf 2 (oPPrime 2 (GiOne Gp β ε))} =
          {W : Subgroup M | ∃ l ∈ oPPrime 2 (GiOne Gp β ε), W = cj l (ctr T)} ∧
        Set.ncard {W : Subgroup M | (∃ g : M, W = cj g (ctr T)) ∧
          W ≤ pCoreOf 2 (oPPrime 2 (GiOne Gp β ε))} = 2 ^ f + 1) ∧
        ({W : Subgroup M | (∃ g : M, W = cj g (ctr T)) ∧ W ≤ pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε))} =
          {W : Subgroup M | ∃ l ∈ oPPrime 2 (GiTwo Gp β ε), W = cj l (ctr T)} ∧
        Set.ncard {W : Subgroup M | (∃ g : M, W = cj g (ctr T)) ∧
          W ≤ pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε))} = 2 ^ f + 1)) ∧
      Subgroup.normalizer (T : Set M) = MiOne β ε ⊓ MiTwo β ε


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Open CFSG.Quasithin

@[expose] def InnDiag3 {E : Type} [Group E] (Gp : Subgroup E) (g : E) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (e : ↥Gp ≃* StatedProj (StatedSL 3 K))
    (A : Matrix.GeneralLinearGroup (Fin 3) K),
    ∀ x y : ↥Gp, (y : E) = g * (x : E) * g⁻¹ →
      ∃ X X' : ↥(StatedSL 3 K), e x = (QuotientGroup.mk X : StatedProj (StatedSL 3 K)) ∧
        e y = (QuotientGroup.mk X' : StatedProj (StatedSL 3 K)) ∧
        (X' : Matrix.GeneralLinearGroup (Fin 3) K) = A * (X : Matrix.GeneralLinearGroup (Fin 3) K) * A⁻¹

@[expose] def BInvMembers {M : Type} [Group M] (B Z Q : Subgroup M) : Set (Subgroup M) :=
  {W | (∃ g : M, W = cj g Z) ∧ W ≤ Q ∧ W ≠ Z ∧ ∀ b ∈ B, cj b W = W}

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def f447Ybar {E : Type} [Group E] (Gp Mi Bbar : Subgroup E) : Subgroup E where
  carrier := {b | b ∈ Bbar ∧
    b ∈ Subgroup.normalizer ((oPPrime 2 (Gp ⊓ Mi) : Subgroup E) : Set E) ∧
    b ∈ Subgroup.normalizer ((pCoreOf 2 (oPPrime 2 (Gp ⊓ Mi)) : Subgroup E) : Set E) ∧
    ∀ x ∈ oPPrime 2 (Gp ⊓ Mi), b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (oPPrime 2 (Gp ⊓ Mi))}
  one_mem' := by
    refine ⟨Bbar.one_mem, Subgroup.one_mem _, Subgroup.one_mem _, fun x _ => ?_⟩
    simp
  mul_mem' := by
    rintro a b ⟨haB, haL, haQ, ha⟩ ⟨hbB, hbL, hbQ, hb⟩
    refine ⟨Bbar.mul_mem haB hbB, Subgroup.mul_mem _ haL hbL, Subgroup.mul_mem _ haQ hbQ,
      fun x hx => ?_⟩
    have h1 : a * b * x * (a * b)⁻¹ * x⁻¹ =
        (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
    rw [h1]
    refine Subgroup.mul_mem _ ?_ (ha x hx)
    exact (Subgroup.mem_normalizer_iff.mp haQ _).mp (hb x hx)
  inv_mem' := by
    rintro a ⟨haB, haL, haQ, ha⟩
    refine ⟨Bbar.inv_mem haB, Subgroup.inv_mem _ haL, Subgroup.inv_mem _ haQ, fun x hx => ?_⟩
    have hy : a⁻¹ * x * a ∈ oPPrime 2 (Gp ⊓ Mi) := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haL) x).mp hx
      simpa using this
    have h1 := ha _ hy
    have h2 : a⁻¹ * x * a * x⁻¹ = (a * (a⁻¹ * x * a) * a⁻¹ * (a⁻¹ * x * a)⁻¹)⁻¹ := by group
    show a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ ∈ _
    rw [inv_inv, h2]
    exact Subgroup.inv_mem _ h1

@[expose] def F_4_47 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → κ = .L3 →
    ∀ Bbar B0bar : Subgroup E, IsHallTwoPrime Bbar (M₁ ⊓ M₂) →
      (∀ b : E, b ∈ B0bar ↔ b ∈ Bbar ∧ InnDiag3 Gp b) →
      (imB β ε (f447Ybar Gp M₂ Bbar) ≠ ⊥ ∨
        (f = 2 ∧ MiOne β ε = oPPrime 2 (GiOne Gp β ε) ∧ MiTwo β ε = oPPrime 2 (GiTwo Gp β ε) ∧
          imB β ε B0bar = imB β ε Bbar ∧ Nat.card ↥(imB β ε Bbar) = 3 ∧
          Odd (Nat.card ↥(Subgroup.centralizer ((imB β ε Bbar : Subgroup M) : Set M))))) ∧
      (imB β ε (f447Ybar Gp M₂ Bbar) ≠ ⊥ →
        imB β ε B0bar = Subgroup.centralizer ((imB β ε B0bar : Subgroup M) : Set M) ∧
        ¬ ∃ g : M, ∀ y ∈ imB β ε (f447Ybar Gp M₂ Bbar),
          g * y * g⁻¹ = y⁻¹) ∧
      imB β ε B0bar = (fittingSubgroup ↥(imB β ε Bbar)).map (imB β ε Bbar).subtype


@[expose] def F_4_48 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → κ = .L3 →
    ∀ T : Subgroup M, IsSylowOf 2 T (MiOne β ε ⊓ MiTwo β ε) →
    ∀ g : M, g ∉ MiOne β ε ⊓ MiTwo β ε →
      (T ⊓ cj g T = ⊥ ∧ Odd (orderOf (z * (g * z * g⁻¹)))) ∨
      (T ⊓ cj g T = ctr T ⊔ cj g (ctr T) ∧
        (T ⊓ cj g T = pCoreOf 2 (oPPrime 2 (GiOne Gp β ε)) ∨
          T ⊓ cj g T = pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε))) ∧
        orderOf (z * (g * z * g⁻¹)) = 2) ∨
      (ctr T ≠ T ⊓ cj g T ∧ cj g (ctr T) ≠ T ⊓ cj g T ∧ (∃ h : M, T ⊓ cj g T = cj h (ctr T)) ∧
        orderOf (z * (g * z * g⁻¹)) = 4)


@[expose] def F_4_49_conditional : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → κ = .L3 →
    ∀ T : Subgroup M, IsSylowOf 2 T (MiOne β ε ⊓ MiTwo β ε) →
    ∀ Bbar : Subgroup E, IsHallTwoPrime Bbar (M₁ ⊓ M₂) →
    ∀ s₁ s₂ : M,
      s₁ ∈ MiOne β ε → s₁ ∈ Subgroup.normalizer ((imB β ε Bbar : Subgroup M) : Set M) →
      s₁ ∉ MiOne β ε ⊓ MiTwo β ε → s₁ * s₁ = 1 →
      s₂ ∈ MiTwo β ε → s₂ ∈ Subgroup.normalizer ((imB β ε Bbar : Subgroup M) : Set M) →
      s₂ ∉ MiOne β ε ⊓ MiTwo β ε → s₂ * s₂ = 1 →
      (cj s₁ (ctr T) ∈ BInvMembers (imB β ε Bbar) (ctr T) (pCoreOf 2 (oPPrime 2 (GiOne Gp β ε))) ∧
        ∀ W ∈ BInvMembers (imB β ε Bbar) (ctr T) (pCoreOf 2 (oPPrime 2 (GiOne Gp β ε))),
          W = cj s₁ (ctr T)) ∧
      (cj s₂ (ctr T) ∈ BInvMembers (imB β ε Bbar) (ctr T) (pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε))) ∧
        ∀ W ∈ BInvMembers (imB β ε Bbar) (ctr T) (pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε))),
          W = cj s₂ (ctr T)) ∧
      (∀ g ∈ Subgroup.normalizer ((imB β ε Bbar : Subgroup M) : Set M),
        (∃ b ∈ imB β ε Bbar, b * g ≠ 1 ∧ (b * g) * (b * g) = 1) ∨ T ⊓ cj g T = T ∨
          T ⊓ cj g T = cj s₁ (ctr T) ∨ T ⊓ cj g T = cj s₂ (ctr T)) ∧
      ((s₁ * s₂) ^ 3 ∈ imB β ε Bbar ∧ s₁ * s₂ ∉ imB β ε Bbar) ∧
      β.IsApartment κ.m {u : β.Γ | ∃ w : β.G0,
        epsG β ε w ∈ Subgroup.closure {s₁, s₂} ⊔ imB β ε Bbar ∧ (u = w • β.xv ∨ u = w • β.lv)}


@[expose] def F_4_49 : Prop :=
  F_4_49_conditional ∧
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → κ = .L3 →
    ∀ Bbar : Subgroup E, IsHallTwoPrime Bbar (M₁ ⊓ M₂) →
    ∃ s₁ s₂ : M,
      s₁ ∈ MiOne β ε ∧ s₁ ∈ Subgroup.normalizer ((imB β ε Bbar : Subgroup M) : Set M) ∧
      s₁ ∉ MiOne β ε ⊓ MiTwo β ε ∧ s₁ * s₁ = 1 ∧
      s₂ ∈ MiTwo β ε ∧ s₂ ∈ Subgroup.normalizer ((imB β ε Bbar : Subgroup M) : Set M) ∧
      s₂ ∉ MiOne β ε ⊓ MiTwo β ε ∧ s₂ * s₂ = 1


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section F423

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

abbrev GHat (M₁ M₂ : Subgroup E) : Type := Amalgam.gp (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam

noncomputable abbrev xi1 (M₁ M₂ : Subgroup E) : ↥M₁ →* GHat M₁ M₂ :=
  Amalgam.ξ (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam RankTwoIndex.one

noncomputable abbrev xi2 (M₁ M₂ : Subgroup E) : ↥M₂ →* GHat M₁ M₂ :=
  Amalgam.ξ (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam RankTwoIndex.two

variable {Y : Type} [Group Y]

noncomputable def liftDom1 (κ : GLKind) (M₁ M₂ : Subgroup E) : Set (GHat M₁ M₂) :=
  if κ = GLKind.Tits then Set.range (xi1 M₁ M₂) else Set.range (xi2 M₁ M₂)

noncomputable def liftDom2 (κ : GLKind) (β : Cpl M₁ M₂ Y) (cc : β.Γ) : Set (GHat M₁ M₂) :=
  if κ = GLKind.Tits then Set.range (xi2 M₁ M₂)
  else {w | ∃ h : ↥M₁, f1 (c := β) h • β.lv = cc ∧ ∃ b : ↥M₂, w = xi1 M₁ M₂ h * xi2 M₁ M₂ b * (xi1 M₁ M₂ h)⁻¹}

noncomputable def N1hat (κ : GLKind) (β : Cpl M₁ M₂ Y) (cc y : β.Γ) : Set (GHat M₁ M₂) :=
  {w | w ∈ liftDom1 κ M₁ M₂ ∧ ∃ g : β.G0, g ∈ N1set β κ cc y ∧ (g : Y) = β.toCompletion.hat w}

noncomputable def N2hat (κ : GLKind) (β : Cpl M₁ M₂ Y) (cc y y' : β.Γ) : Set (GHat M₁ M₂) :=
  {w | w ∈ liftDom2 κ β cc ∧ ∃ g : β.G0, g ∈ N2set β κ cc y y' ∧ (g : Y) = β.toCompletion.hat w}

noncomputable def PhatFor {Y' : Type} [Group Y'] (κ : GLKind) (β : Cpl M₁ M₂ Y) (cc y y' : β.Γ)
    (ρ : Cpl M₁ M₂ Y') : Set (GHat M₁ M₂ × GHat M₁ M₂) :=
  {st | st.1 ∈ N1hat κ β cc y ∧ st.2 ∈ N2hat κ β cc y y' ∧
    orderOf (ρ.toCompletion.hat st.1 * ρ.toCompletion.hat st.2) = m0Of κ}

structure HypF_4_23F (κ : GLKind) {F : Type} [Group F] (j : E →* F) (M₁ M₂ : Subgroup E)
    (F₁ F₂ : Subgroup F) : Prop where
  inj : Function.Injective j
  index_two : j.range.index = 2
  lie : IsGenLie F (if κ = GLKind.G2d then GLKind.G2 else GLKind.F4tw) 2 1
  amalgam : HypF_4_4 (if κ = GLKind.G2d then GLKind.G2 else GLKind.F4tw) 2 1 (⊤ : Subgroup F) F₁ F₂
  sylow : IsSylowOf 2 (F₁ ⊓ F₂) ⊤
  le₁ : M₁.map j ≤ F₁
  le₂ : M₂.map j ≤ F₂
  normal₁ : ∀ f ∈ F₁, ∀ x ∈ M₁, f * j x * f⁻¹ ∈ M₁.map j
  normal₂ : ∀ f ∈ F₂, ∀ x ∈ M₂, f * j x * f⁻¹ ∈ M₂.map j
  split₁ : ∀ f ∈ F₁, ∃ u ∈ F₁ ⊓ F₂, ∃ x ∈ M₁, f = u * j x
  split₂ : ∀ f ∈ F₂, ∃ u ∈ F₁ ⊓ F₂, ∃ x ∈ M₂, f = u * j x

end F423

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def F_4_23 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → Gp = ⊤ → (κ = .G2d ∨ κ = .Tits) →
    (∃ (Y₁ Y₂ : Type) (_ : Group Y₁) (_ : Group Y₂) (β₁ : Cpl M₁ M₂ Y₁) (β₂ : Cpl M₁ M₂ Y₂),
      β₁.IsFaithful ∧ β₂.IsFaithful ∧ β₁.IsSmall κ.m ∧ β₂.IsSmall κ.m ∧
      ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
        Amalgam.Completion.IsEquivalent β.toCompletion β₁.toCompletion ∨
          Amalgam.Completion.IsEquivalent β.toCompletion β₂.toCompletion) ∧
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
      ∀ cc ∈ CosetGeom.nbrs β.xv, cc ≠ β.lv →
      ∀ y ∈ CosetGeom.nbrs β.lv, y ≠ β.xv →
      ∀ y' ∈ CosetGeom.nbrs cc, y' ≠ β.xv →
      ∀ (Y' : Type) [Group Y'] (ρ : Cpl M₁ M₂ Y'), ρ.IsFaithful →
        (ρ.IsSmall κ.m ↔ (PhatFor κ β cc y y' ρ).Nonempty) ∧
        (∀ st ∈ PhatFor κ β cc y y' β, st ∈ PhatFor κ β cc y y' ρ →
          β.toCompletion.hat.ker = Subgroup.normalClosure
            {(st.1 * st.2) ^ m0Of κ} ∧
          Subgroup.normalClosure {(st.1 * st.2) ^ m0Of κ} = ρ.toCompletion.hat.ker ∧
          Amalgam.Completion.IsEquivalent β.toCompletion ρ.toCompletion) ∧
        ((PhatFor κ β cc y y' β ∩ PhatFor κ β cc y y' ρ).Nonempty →
          Amalgam.Completion.IsEquivalent β.toCompletion ρ.toCompletion) ∧
        (∀ (F : Type) [Group F] (j : E →* F) (F₁ F₂ : Subgroup F), HypF_4_23F κ j M₁ M₂ F₁ F₂ →
          (∀ u ∈ F₁ ⊓ F₂, ∃ φ : β.G0 ≃* β.G0,
            (∀ a a' : ↥M₁, j (a' : E) = u * j (a : E) * u⁻¹ →
              φ (f1 (c := β) a) = f1 (c := β) a') ∧
            (∀ b b' : ↥M₂, j (b' : E) = u * j (b : E) * u⁻¹ →
              φ (f2 (c := β) b) = f2 (c := β) b') ∧
            (∀ d d' : ↥(M₁ ⊓ M₂), j (d' : E) = u * j (d : E) * u⁻¹ →
              φ (bmap β d) = bmap β d')) →
          ∀ ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂), ι = incl M₁ M₂ →
            Amalgam.Completion.IsQuasiEquivalent β.toCompletion ι.toCompletion)

end CFSG.ASVolI

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def F_4_3 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4g κ p f Gp M₁ M₂ →
    (κ = .G2d → IsGenLie (MulAut ↥Gp) .G2 2 1) ∧ (κ = .Tits → IsGenLie (MulAut ↥Gp) .F4tw 2 1) ∧
    (IsLieExtAmalgam M₁ M₂ ∨ (Gp = ⊤ ∧ (κ = .G2d ∨ κ = .Tits)))

@[expose] def F_4_4 : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ →
    IsSylowOf p (pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))) Gp ∧
    ((Gp = ⊤ ∧ κ = .G2d) → (RankTwoAmalgam.ofSubgroups M₁ M₂).qOne = 2 ∧
      (RankTwoAmalgam.ofSubgroups M₁ M₂).qTwo = 2) ∧
    ((Gp = ⊤ ∧ κ = .Tits) → (RankTwoAmalgam.ofSubgroups M₁ M₂).qOne = 4 ∧
      (RankTwoAmalgam.ofSubgroups M₁ M₂).qTwo = 2)

@[expose] def F_4_25 : Prop :=
  ∀ (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 GLKind.G2d p f Gp M₁ M₂ → Gp = ⊤ →
    ∀ s ∈ M₁, s * s = 1 → s ∈ pCoreOf p M₁


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section FieldGraph

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {E : Type} [Group E]


@[expose] def cenIn (Gp : Subgroup E) (t : E) : Subgroup E :=
  Gp ⊓ Subgroup.centralizer ({t} : Set E)


@[expose] def HasMatrixFieldAction {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Type) [Field K] (H : Subgroup (Matrix.GeneralLinearGroup ι K))
    (Gp : Subgroup E) (t : E) (σ : K →+* K) : Prop :=
  ∃ e : ↥Gp ≃* StatedProj H, ∀ x : ↥Gp, ∃ y : ↥Gp,
    (y : E) = t * (x : E) * t⁻¹ ∧
      ∀ A : ↥H, e x = (QuotientGroup.mk A : StatedProj H) →
        ∃ B : ↥H, e y = (QuotientGroup.mk B : StatedProj H) ∧
          ((B : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) =
            (((A : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).map σ)

@[expose] def HasChevalleyFieldAction (τ : Tag) (K : Type) [Field K]
    (H : Subgroup (ModGL τ K)) (Gp : Subgroup E) (t : E) (σ : K →+* K) : Prop :=
  ∃ e : ↥Gp ≃* (↥H ⧸ Subgroup.center ↥H), ∀ x : ↥Gp, ∃ y : ↥Gp,
    (y : E) = t * (x : E) * t⁻¹ ∧
      ∀ A : ↥H, e x = (QuotientGroup.mk A : ↥H ⧸ Subgroup.center ↥H) →
        ∃ B : ↥H, e y = (QuotientGroup.mk B : ↥H ⧸ Subgroup.center ↥H) ∧
          ((B : ModGL τ K) : Module.End K (RootModule τ K)) =
            entrywise σ ((A : ModGL τ K) : Module.End K (RootModule τ K))

@[expose] def IsFieldInv (κ : GLKind) (f : ℕ) (Gp : Subgroup E) (t : E) : Prop :=
  t ∉ Gp ∧ t * t = 1 ∧ ∃ f₀ : ℕ, 0 < f₀ ∧ f = 2 * f₀ ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K),
      (∀ a : K, σ a = a ^ (2 ^ (if κ = GLKind.D4tw then 3 * f₀ else f₀))) ∧
        match κ with
        | .L3 => Nat.card K = 2 ^ f ∧ HasMatrixFieldAction K (StatedSL 3 K) Gp t σ
        | .Sp4 => Nat.card K = 2 ^ f ∧ HasMatrixFieldAction K (StatedSp 2 K) Gp t σ
        | .G2 => Nat.card K = 2 ^ f ∧ HasChevalleyFieldAction Tag.G2 K (adjointGroup Tag.G2 K) Gp t σ
        | .D4tw => Nat.card K = (2 ^ f) ^ 3 ∧
            ∃ twist : K →+* K, (∀ a : K, twist a = a ^ (2 ^ f)) ∧
              HasChevalleyFieldAction TwistTag.D4.tag K ⁅CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K twist,
                CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K twist⁆ Gp t σ
        | _ => False

@[expose] def HasUnitaryGraphAction (n q : ℕ) (K : Type) [Field K]
    (Gp : Subgroup E) (t : E) : Prop :=
  ∃ σ : K →+* K, (∀ a : K, σ a = a ^ q) ∧
    ∃ changeBasis : Matrix.GeneralLinearGroup (Fin n) K,
      (n = 4 →
        (Matrix.transpose ((changeBasis : Matrix (Fin n) (Fin n) K).map σ) *
          (changeBasis : Matrix (Fin n) (Fin n) K)) =
            Matrix.of (fun i j => if (i.val, j.val) = (0, 2) ∨ (i.val, j.val) = (1, 3) ∨
              (i.val, j.val) = (2, 0) ∨ (i.val, j.val) = (3, 1) then 1 else 0)) ∧
      (n ≠ 4 → changeBasis = 1) ∧
      ∃ e : ↥Gp ≃* StatedProj (StatedSU n q K), ∀ x : ↥Gp, ∃ y : ↥Gp,
    (y : E) = t * (x : E) * t⁻¹ ∧
      ∀ A : ↥(StatedSU n q K),
        e x = (QuotientGroup.mk A : StatedProj (StatedSU n q K)) →
          ∃ B : ↥(StatedSU n q K),
            e y = (QuotientGroup.mk B : StatedProj (StatedSU n q K)) ∧
              (B : Matrix.GeneralLinearGroup (Fin n) K) =
                changeBasis * (Matrix.GeneralLinearGroup.map σ changeBasis)⁻¹ *
                  Matrix.GeneralLinearGroup.map σ (A : Matrix.GeneralLinearGroup (Fin n) K) *
                    Matrix.GeneralLinearGroup.map σ changeBasis * changeBasis⁻¹

@[expose] def IsGraphInv (κ : GLKind) (f : ℕ) (Gp : Subgroup E) (t : E) : Prop :=
  t ∉ Gp ∧ t * t = 1 ∧ 0 < f ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ f) ^ 2 ∧
      ((κ = GLKind.U4 ∧ HasUnitaryGraphAction 4 (2 ^ f) K Gp t) ∨
        (κ = GLKind.U5 ∧ HasUnitaryGraphAction 5 (2 ^ f) K Gp t))

@[expose] def IsSp4LongRootInv (C : Subgroup E) (z : E) : Prop :=
  z ∈ C ∧ z ≠ 1 ∧ z * z = 1 ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (e : ↥C ≃* StatedProj (StatedSp 2 K)),
      ∀ x : ↥C, (x : E) = z → ∃ A : ↥(StatedSp 2 K),
        e x = (QuotientGroup.mk A : StatedProj (StatedSp 2 K)) ∧
        Matrix.rank (((A : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - 1) = 1

@[expose] def IsTypeIIIInv (κ : GLKind) (f : ℕ) (Gp : Subgroup E) (t : E) : Prop :=
  κ = GLKind.U4 ∧ ∃ s z : E, t = s * z ∧ IsGraphInv κ f Gp s ∧ IsSp4LongRootInv (cenIn Gp s) z ∧
    s * z = z * s


def NativeRepresentativeAction {Representatives Model : Type}
    [Group Representatives] [Group Model] (Gp : Subgroup E)
    (quotient : Representatives →* Model) (identification : Model ≃* Gp)
    (operator : Representatives → Representatives → Prop) (actor : E) : Prop :=
  ∀ representative, ∃ image, operator representative image ∧
    (identification (quotient image) : E) =
      actor * (identification (quotient representative) : E) * actor⁻¹

def NativeMatrixOperator {index : Type} [Fintype index] [DecidableEq index]
    {K : Type} [Field K] (group : Subgroup (Matrix.GeneralLinearGroup index K))
    (sigma : K →+* K) (source target : group) : Prop :=
  (target : Matrix.GeneralLinearGroup index K).val =
    (source : Matrix.GeneralLinearGroup index K).val.map sigma

def NativeChevalleyOperator {tag : Tag} {K : Type} [Field K]
    (group : Subgroup (ModGL tag K)) (sigma : K →+* K)
    (source target : group) : Prop :=
  ((target : ModGL tag K) : Module.End K (RootModule tag K)) =
    entrywise sigma ((source : ModGL tag K) : Module.End K (RootModule tag K))

def NativeCoordinates.PureFieldAction {kind : GLKind} {degree : ℕ} {Gp : Subgroup E}
    (coordinates : NativeCoordinates kind 2 degree Gp) (subdegree : ℕ)
    (actor : E) : Prop :=
  match coordinates with
  | .classical modelKind _ marking =>
      (modelKind = .L3 ∨ modelKind = .Sp4) ∧
      ∃ sigma : marking.field →+* marking.field,
        (∀ parameter, sigma parameter = parameter ^ (2 ^ subdegree)) ∧
        NativeRepresentativeAction Gp
          (ClassicalRoots.projectiveMap modelKind (2 ^ degree) marking.field)
          marking.identification
          (NativeMatrixOperator (ClassicalRoots.nativeGroup modelKind (2 ^ degree)
            marking.field) sigma) actor
  | @NativeCoordinates.g2 _ _ _ _ _ _ _ _ K fieldK finiteK _ identification =>
      letI := fieldK
      letI := finiteK
      ∃ sigma : K →+* K,
        (∀ parameter, sigma parameter = parameter ^ (2 ^ subdegree)) ∧
        NativeRepresentativeAction Gp
          (QuotientGroup.mk' (Subgroup.center (G2Native.Parent K))) identification
          (NativeChevalleyOperator (adjointGroup .G2 K) sigma) actor
  | @NativeCoordinates.triality _ _ _ _ _ _ K fieldK finiteK twist _ identification =>
      letI := fieldK
      letI := finiteK
      ∃ sigma : K →+* K,
        (∀ parameter, sigma parameter = parameter ^ (2 ^ (3 * subdegree))) ∧
        NativeRepresentativeAction Gp
          (QuotientGroup.mk' (Subgroup.center ↥⁅CFSG.Blueprint.twistedFixedGroup .D4 K twist,
            CFSG.Blueprint.twistedFixedGroup .D4 K twist⁆)) identification
          (NativeChevalleyOperator ⁅CFSG.Blueprint.twistedFixedGroup .D4 K twist,
            CFSG.Blueprint.twistedFixedGroup .D4 K twist⁆ sigma) actor
  | _ => False

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

def NativeCoordinates.RankInvolution {kind : GLKind} {degree : ℕ} {Gp : Subgroup E}
    (coordinates : NativeCoordinates kind 2 degree Gp) (rank : ℕ) (element : E) : Prop :=
  match coordinates with
  | .classical modelKind _ marking =>
      element ∈ Gp ∧ element ≠ 1 ∧ element * element = 1 ∧
      ∃ representative : ClassicalRoots.nativeGroup modelKind (2 ^ degree) marking.field,
        (marking.transport representative : E) = element ∧
        representative * representative = 1 ∧
        Matrix.rank ((representative : Matrix.GeneralLinearGroup
          (ClassicalRoots.Coord modelKind) marking.field).val - 1) = rank
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

def NativeCoordinates.FieldAction {kind : GLKind} {degree : ℕ} {Gp : Subgroup E}
    (coordinates : NativeCoordinates kind 2 degree Gp) (subdegree : ℕ)
    (actor : E) : Prop :=
  ∃ conjugacy : MulAut Gp, coordinates.InnerDiagonal conjugacy ∧
    (coordinates.transport conjugacy).PureFieldAction subdegree actor

def NativeCoordinates.GraphAction {kind : GLKind} {degree : ℕ} {Gp : Subgroup E}
    (coordinates : NativeCoordinates kind 2 degree Gp) (actor : E) : Prop :=
  ∃ conjugacy : MulAut Gp, coordinates.InnerDiagonal conjugacy ∧
    (coordinates.transport conjugacy).PureGraphAction actor

def NativeChart.IsFieldInv {kind : GLKind} {degree : ℕ} {Gp : Subgroup E}
    (chart : NativeChart kind 2 degree Gp) (actor : E) : Prop :=
  actor ∉ Gp ∧ actor * actor = 1 ∧ ∃ subdegree,
    0 < subdegree ∧ degree = 2 * subdegree ∧
      chart.coordinatePayload.FieldAction subdegree actor

def NativeChart.IsGraphInv {kind : GLKind} {degree : ℕ} {Gp : Subgroup E}
    (chart : NativeChart kind 2 degree Gp) (actor : E) : Prop :=
  actor ∉ Gp ∧ actor * actor = 1 ∧ 0 < degree ∧
    chart.coordinatePayload.GraphAction actor

def NativeChart.IsTypeIIIInv {kind : GLKind} {degree : ℕ} {Gp : Subgroup E}
    (chart : NativeChart kind 2 degree Gp) (actor : E) : Prop :=
  kind = .U4 ∧ ∃ graph root : E, actor = graph * root ∧
    chart.IsGraphInv graph ∧ chart.coordinatePayload.RankInvolution 1 root ∧
    graph * root = root * graph

def NativeChart.GraphFixedMarkingGoal {kind : GLKind} {degree : ℕ} {Gp : Subgroup E}
    (chart : NativeChart kind 2 degree Gp) (actor : E) : Prop :=
  chart.IsGraphInv actor →
    ∃ marking : ClassicalRoots.Marking .Sp4 2 degree (cenIn Gp actor),
      ∀ (element : E) (hElement : element ∈ cenIn Gp actor),
        (chart.coordinatePayload.RankInvolution 1 element ↔
          element ≠ 1 ∧ element * element = 1 ∧
          ∃ conjugator : cenIn Gp actor,
            conjugator * ⟨element, hElement⟩ * conjugator⁻¹ ∈
              marking.root .longOne false)


end FieldGraph

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def F_4_29 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    ∀ hyp : HypF_4_4 κ 2 f Gp M₁ M₂, κ.IsLie →
    let chart := hyp.toHypF_4_4g.chart
    ∀ T : Subgroup E, IsSylowOf 2 T (M₁ ⊓ M₂) →
      (f = 1 → Gp = ⊤ ∨ (κ = .D4tw ∧ Gp.index = 3 ∧ Nat.card E = Nat.card (MulAut ↥Gp)) ∨
        ((κ = .U4 ∨ κ = .U5) ∧ Gp.index = 2 ∧ Nat.card E = Nat.card (MulAut ↥Gp))) ∧
      ((∃ t ∈ T, T = Subgroup.zpowers t ⊔ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧
        (∃ H : Subgroup E, IsComplementIn H (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) T) ∧
        ∀ t ∈ T, t ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → t * t = 1 →
          chart.IsFieldInv t ∨
            (chart.IsGraphInv t ∧ IsGenLie ↥(cenIn Gp t) GLKind.Sp4 2 f ∧
              chart.GraphFixedMarkingGoal t) ∨
            (chart.IsTypeIIIInv t ∧ ∃ s z : E,
              t = s * z ∧ chart.IsGraphInv s ∧
                chart.coordinatePayload.RankInvolution 1 z ∧ s * z = z * s ∧
                IsGenLie ↥(cenIn Gp s) .Sp4 2 f ∧ chart.GraphFixedMarkingGoal s ∧
                Subgroup.centralizer ({t} : Set E) =
                  Subgroup.centralizer ({s} : Set E) ⊓ Subgroup.centralizer ({z} : Set E))) ∧
      (2 ≤ f → oPPrime 2 (Gp ⊓ M₁) = perfectCore (Gp ⊓ M₁) ∧
        oPPrime 2 (Gp ⊓ M₂) = perfectCore (Gp ⊓ M₂)) ∧
      (pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ∧ pCoreOf 2 M₁ = pCoreOf 2 (Gp ⊓ M₁) ∧
        pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂)) ∧
      ((pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁) ⊔ T) = pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁)) ∧
          pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂) ⊔ T) = pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂))) ∨
        (κ = .U4 ∧ ∃ D : Subgroup E, Gp ≤ D ∧ Gp.relIndex D = 2 ∧ (D ⊓ M₁) ⊔ (D ⊓ M₂) = D ∧
          ∃ t ∈ T, t ∈ D ∧ chart.IsGraphInv t ∧
            (pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁))).relIndex (pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁) ⊔ T)) = 2 ∧
            pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁) ⊔ T) =
              pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁)) ⊔ Subgroup.zpowers t ∧
            pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂) ⊔ T) = pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂)))) ∧
      ((thompsonJ T = thompsonJ (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧
          baum T = baum (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) ∨ (f = 1 ∧ (κ = .U4 ∨ κ = .U5))) ∧
      (ctr T = ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ⊓ Subgroup.centralizer (T : Set E) ∧
        (ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = ctr (oPPrime 2 (Gp ⊓ M₁)) ∨
          (κ = .L3 ∧ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = chart.longRoot) ∨
          (κ = .Sp4 ∧ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) =
            ctr (oPPrime 2 (Gp ⊓ M₁)) ⊔ ctr (oPPrime 2 (Gp ⊓ M₂)) ∧
            ctr (oPPrime 2 (Gp ⊓ M₁)) ⊓ ctr (oPPrime 2 (Gp ⊓ M₂)) = ⊥ ∧
            ctr (oPPrime 2 (Gp ⊓ M₁)) = chart.longRoot ∧
            ctr (oPPrime 2 (Gp ⊓ M₂)) = chart.shortRoot))) ∧
      (∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
        ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp).subgroupOf (M₁ ⊓ M₂)).map (bmap β) ≤
          oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
            ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β))) ∧
        (Sp 2 Gp β ≤ oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
              ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β))) ∨
          (f = 1 ∧ (κ = .Sp4 ∨ κ = .G2 ∨ κ = .F4tw) ∧
            (Sp 2 Gp β ⊓ oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
              ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β)))).relIndex (Sp 2 Gp β) = 2)))

@[expose] def F_4_36 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    ∀ hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z,
    (κ = .U4 ∨ κ = .U5) → f = 1 →
    let chart := hyp.amalgam.toHypF_4_4g.chart
    ∀ Tb : Subgroup E, IsSylowOf 2 Tb (M₁ ⊓ M₂) →
    ∀ fb : ↥(M₁ ⊓ M₂), (fb : E) ∈ Tb → chart.IsGraphInv (fb : E) →
      ¬ IsConj z (bM β ε fb)


end CFSG.ASVolI

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam

variable {E Y : Type} [Group E] [Group Y]

@[expose] def f437Dbar (Gp : Subgroup E) (fb : E) : Subgroup E :=
  cenIn Gp fb

@[expose] def f437DbarOne (Gp M₁ : Subgroup E) (fb : E) : Subgroup E :=
  cenIn (Gp ⊓ M₁) fb

@[expose] def f437DbarTwo (Gp M₂ : Subgroup E) (fb : E) : Subgroup E :=
  cenIn (Gp ⊓ M₂) fb

@[expose] def f437Delta (Gp M₁ M₂ : Subgroup E) (fb : E) : RankTwoAmalgam :=
  RankTwoAmalgam.ofSubgroups (f437DbarOne Gp M₁ fb) (f437DbarTwo Gp M₂ fb)

@[expose] def f437Left (Gp : Subgroup E) {M₁ M₂ : Subgroup E}
    (β : Cpl M₁ M₂ Y) (fb : E) : f437DbarOne Gp M₁ fb →* Y :=
  β.φ1.comp (Subgroup.inclusion
    ((inf_le_left : (Gp ⊓ M₁) ⊓ Subgroup.centralizer ({fb} : Set E) ≤ Gp ⊓ M₁).trans
      inf_le_right))

@[expose] def f437Right (Gp : Subgroup E) {M₁ M₂ : Subgroup E}
    (β : Cpl M₁ M₂ Y) (fb : E) : f437DbarTwo Gp M₂ fb →* Y :=
  β.φ2.comp (Subgroup.inclusion
    ((inf_le_left : (Gp ⊓ M₂) ⊓ Subgroup.centralizer ({fb} : Set E) ≤ Gp ⊓ M₂).trans
      inf_le_right))

@[expose] def f437D (Gp : Subgroup E) {M₁ M₂ : Subgroup E}
    (β : Cpl M₁ M₂ Y) (fb : E) : Subgroup Y :=
  (f437Left Gp β fb).range ⊔ (f437Right Gp β fb).range

@[expose] def f437Ebar (fb : E) : Subgroup E :=
  Subgroup.centralizer ({fb} : Set E)

@[expose] def f437EbarOne (M₁ : Subgroup E) (fb : E) : Subgroup E :=
  cenIn M₁ fb

@[expose] def f437EbarTwo (M₂ : Subgroup E) (fb : E) : Subgroup E :=
  cenIn M₂ fb

@[expose] def F437RestrictionAssembly (Gp M₁ M₂ : Subgroup E)
    (β : Cpl M₁ M₂ Y) (fb : E) : Prop :=
  f437DbarOne Gp M₁ fb ⊔ f437DbarTwo Gp M₂ fb = f437Dbar Gp fb ∧
  f437DbarOne Gp M₁ fb ⊓ f437DbarTwo Gp M₂ fb =
    cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb ∧
  IsLieParabolics 2 (f437Dbar Gp fb) (cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb)
    (f437DbarOne Gp M₁ fb) (f437DbarTwo Gp M₂ fb) ∧
  ∃ restriction : (f437Delta Gp M₁ M₂ fb).Completion (f437D Gp β fb),
    restriction.IsFaithful ∧
    (∀ generator, (restriction.φ1 generator : Y) = f437Left Gp β fb generator) ∧
    (∀ generator, (restriction.φ2 generator : Y) = f437Right Gp β fb generator) ∧
    (∀ edge, (restriction.φ12 edge : Y) =
      f437Left Gp β fb ((f437Delta Gp M₁ M₂ fb).α1 edge))

@[expose] def F437QuotientAssembly (Gp M₁ M₂ : Subgroup E) (fb : E)
    (kind : GLKind) (degree : ℕ) : Prop :=
  ∃ centralInv : f437Ebar fb, (centralInv : E) = fb ∧
    centralInv ≠ 1 ∧ centralInv * centralInv = 1 ∧
    Subgroup.zpowers centralInv ≤ Subgroup.center (f437Ebar fb) ∧
    ∃ normalKernel : (Subgroup.zpowers centralInv).Normal,
      letI := normalKernel
      let quotientMap := QuotientGroup.mk' (Subgroup.zpowers centralInv)
      let localOne := ((f437EbarOne M₁ fb).subgroupOf (f437Ebar fb)).map quotientMap
      let localTwo := ((f437EbarTwo M₂ fb).subgroupOf (f437Ebar fb)).map quotientMap
      let localEdge := ((cenIn (M₁ ⊓ M₂) fb).subgroupOf (f437Ebar fb)).map quotientMap
      let originalD := (f437Dbar Gp fb).subgroupOf (f437Ebar fb)
      let nativeImage := originalD.map quotientMap
      IsGenLie (f437Dbar Gp fb) kind 2 degree ∧
      (∃ marking : f437Dbar Gp fb ≃* nativeImage,
        ∀ element, (marking element : f437Ebar fb ⧸ Subgroup.zpowers centralInv) =
          quotientMap (Subgroup.inclusion
            (inf_le_right : Gp ⊓ f437Ebar fb ≤ f437Ebar fb) element)) ∧
      Function.Injective (quotientMap.comp
        (Subgroup.inclusion (inf_le_right : Gp ⊓ f437Ebar fb ≤ f437Ebar fb))) ∧
      IsLieExtBy (f437Ebar fb ⧸ Subgroup.zpowers centralInv) nativeImage kind 2 degree ∧
      localOne ⊔ localTwo = ⊤ ∧
      (∀ element : f437Ebar fb ⧸ Subgroup.zpowers centralInv,
        ∃ inner ∈ nativeImage, ∃ edge ∈ localEdge, element = inner * edge) ∧
      localOne ⊓ localTwo = localEdge ∧
      nativeImage ⊓ localOne =
        ((f437DbarOne Gp M₁ fb).subgroupOf (f437Ebar fb)).map quotientMap ∧
      nativeImage ⊓ localTwo =
        ((f437DbarTwo Gp M₂ fb).subgroupOf (f437Ebar fb)).map quotientMap ∧
      nativeImage ⊓ localEdge =
        ((cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb).subgroupOf (f437Ebar fb)).map quotientMap ∧
      IsLieParabolics 2 nativeImage (nativeImage ⊓ localEdge)
        (nativeImage ⊓ localOne) (nativeImage ⊓ localTwo) ∧
      (∀ element : f437Ebar fb ⧸ Subgroup.zpowers centralInv,
        element ∈ Subgroup.normalizer ((nativeImage ⊓ localEdge :
          Subgroup (f437Ebar fb ⧸ Subgroup.zpowers centralInv)) : Set _) →
        element ∈ Subgroup.normalizer ((nativeImage ⊓ localOne :
          Subgroup (f437Ebar fb ⧸ Subgroup.zpowers centralInv)) : Set _)) ∧
      ∃ extensionCompletion : (RankTwoAmalgam.ofSubgroups localOne localTwo).Completion
          (f437Ebar fb ⧸ Subgroup.zpowers centralInv),
        extensionCompletion.IsFaithful ∧
        (∀ generator, extensionCompletion.φ1 generator = generator.val) ∧
        (∀ generator, extensionCompletion.φ2 generator = generator.val) ∧
        (∀ edge, extensionCompletion.φ12 edge = edge.val)


end CFSG.ASVolI.ChF

namespace CFSG.ASVolI


open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion ChF

@[expose] def F_4_37 : Prop :=
  ∀ (κ : GLKind) (degree : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E)
    (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y) (M : Type) [Group M]
    (ε : Y →* M) (z : M) (hyp : HypF_4_31 κ degree Gp M₁ M₂ β ε z),
    let chart := hyp.amalgam.toHypF_4_4g.chart
    ∀ Tb : Subgroup E, IsSylowOf 2 Tb (M₁ ⊓ M₂) →
    ∀ fb : ↥(M₁ ⊓ M₂), (fb : E) ∈ Tb →
      (fb : E) ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (fb : E) * (fb : E) = 1 → ¬ chart.IsTypeIIIInv (fb : E) →
      IsSylowOf 2
        (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(fb : E)} : Set E))
        (cenIn Gp (fb : E)) →
      (chart.IsFieldInv (fb : E) ∨ chart.IsGraphInv (fb : E)) ∧
      ((∃ subdegree, 0 < subdegree ∧ degree = 2 * subdegree ∧
          chart.IsFieldInv (fb : E) ∧
          IsGenLie (f437Dbar Gp (fb : E)) κ 2 subdegree ∧
          F437QuotientAssembly Gp M₁ M₂ (fb : E) κ subdegree) ∨
        (chart.IsGraphInv (fb : E) ∧ (κ = .U4 ∨ κ = .U5) ∧
          IsGenLie (f437Dbar Gp (fb : E)) .Sp4 2 degree ∧
          chart.GraphFixedMarkingGoal (fb : E) ∧
          F437QuotientAssembly Gp M₁ M₂ (fb : E) .Sp4 degree)) ∧
      F437RestrictionAssembly Gp M₁ M₂ β (fb : E) ∧
      (((f437DbarOne Gp M₁ (fb : E)).subgroupOf M₁).map (f1 (c := β)) ⊓
          ((f437DbarTwo Gp M₂ (fb : E)).subgroupOf M₂).map (f2 (c := β)) =
        ((cenIn (Gp ⊓ (M₁ ⊓ M₂)) (fb : E)).subgroupOf (M₁ ⊓ M₂)).map (bmap β)) ∧
      ((∀ e ∈ f437Ebar (fb : E), ∀ d ∈ f437Dbar Gp (fb : E),
          e * d * e⁻¹ ∈ f437Dbar Gp (fb : E)) ∧
        Subgroup.centralizer ((f437Dbar Gp (fb : E) : Subgroup E) : Set E) ⊓
          f437Ebar (fb : E) = Subgroup.zpowers (fb : E) ∧
        (∀ e ∈ f437Ebar (fb : E), ∃ d ∈ f437Dbar Gp (fb : E),
          ∃ h ∈ f437Ebar (fb : E) ⊓ (M₁ ⊓ M₂), e = d * h) ∧
        (∀ e ∈ f437Ebar (fb : E),
          e ∈ Subgroup.normalizer ((cenIn (Gp ⊓ (M₁ ⊓ M₂)) (fb : E) : Subgroup E) : Set E) →
          e ∈ Subgroup.normalizer ((f437DbarOne Gp M₁ (fb : E) : Subgroup E) : Set E))) ∧
      (IsSylowOf 2 (imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε fb} : Set M))
          (Subgroup.centralizer ({bM β ε fb} : Set M)) ∨
        (κ = .U4 ∧ degree = 1 ∧ Nonempty (E ≃* MulAut Gp) ∧
          Nonempty (E ≃* β.G0) ∧ IsL43 M))


end CFSG.ASVolI

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF

@[expose] def F_4_44 : Prop := F_4_44_partial


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
