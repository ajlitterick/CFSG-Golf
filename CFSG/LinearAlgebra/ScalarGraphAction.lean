module

public import TauCeti.FieldTheory.Finite.MinpolyOrbit
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped Pointwise

namespace CFSG.ScalarGraphAction

variable {F P : Type*} [Field F] [AddGroup P]


@[expose] def scalarGraphHom {F P : Type*} [Field F] [Group P]
    (φ : P →* Multiplicative (F)) (a : F) :
    P →* Multiplicative (F) × P where
  toFun p := (Multiplicative.ofAdd (a * (φ p).toAdd), p)
  map_one' := by
    ext <;> simp
  map_mul' := by
    intro p q
    apply Prod.ext
    · change Multiplicative.ofAdd (a * (φ (p * q)).toAdd) =
        Multiplicative.ofAdd (a * (φ p).toAdd) *
          Multiplicative.ofAdd (a * (φ q).toAdd)
      rw [map_mul φ, toAdd_mul, ← ofAdd_add, mul_add]
    · rfl


@[expose] def scalarGraph (φ : P →+ F) (a : F) : AddSubgroup (F × P) :=
  (AddMonoidHom.prod ((AddMonoidHom.mulLeft a).comp φ) (AddMonoidHom.id P)).range

@[simp]
theorem mem_scalarGraph (φ : P →+ F) (a x : F) (p : P) :
    (x, p) ∈ scalarGraph φ a ↔ x = a * φ p := by
  constructor
  · rintro ⟨q, hq⟩
    have h1 : a * φ q = x := by
      simpa using congrArg Prod.fst hq
    have h2 : q = p := by
      simpa using congrArg Prod.snd hq
    simpa [h2] using h1.symm
  · intro hx
    refine ⟨p, ?_⟩
    ext <;> simp [hx]


theorem sigma_unique
    (φ : P →+ F) (hφ : Function.Injective φ) [Nontrivial P]
    (f : (F × P) →+ (F × P))
    (σ τ : F ≃ F)
    (hσ : ∀ a : F, (scalarGraph φ a).map f = scalarGraph φ (σ a))
    (hτ : ∀ a : F, (scalarGraph φ a).map f = scalarGraph φ (τ a)) :
    σ = τ := by
  apply Equiv.ext
  intro a
  obtain ⟨p0, hp0⟩ := exists_ne (0 : P)
  have hφp0 : φ p0 ≠ 0 := by
    intro h
    exact hp0 (hφ (by simpa using h))
  have hG : scalarGraph φ (σ a) = scalarGraph φ (τ a) := by
    rw [← hσ a, hτ a]
  have hmem : (τ a * φ p0, p0) ∈ scalarGraph φ (σ a) := by
    rw [hG]
    exact (mem_scalarGraph φ (τ a) (τ a * φ p0) p0).2 rfl
  have h := (mem_scalarGraph φ (σ a) (τ a * φ p0) p0).1 hmem
  exact (mul_right_cancel₀ hφp0 h).symm


section Coordinate

variable {K P W : Type*} [Field K] [Group P] [Group W]

@[expose]
def prodCoordEquiv : (K × Additive P) ≃+ Additive (Multiplicative K × P) :=
  ((AddEquiv.additiveMultiplicative K).symm.prodCongr
      (AddEquiv.refl (Additive P))).trans
    (AddEquiv.prodAdditive (G := Multiplicative K) (H := P)).symm

@[simp]
theorem prodCoordEquiv_apply (x : K) (p : Additive P) :
    prodCoordEquiv (K := K) (P := P) (x, p) =
      Additive.ofMul (Multiplicative.ofAdd x, Additive.toMul p) := by
  rfl

@[simp]
theorem prodCoordEquiv_symm_apply (x : K) (p : P) :
    (prodCoordEquiv (K := K) (P := P)).symm
        (Additive.ofMul (Multiplicative.ofAdd x, p)) = (x, Additive.ofMul p) := by
  rfl

@[expose]
def coordinateAddEquiv (eW : W ≃* (Multiplicative K × P)) (τ : MulAut W) :
    (K × Additive P) ≃+ (K × Additive P) :=
  (prodCoordEquiv (K := K) (P := P)).trans
    (((MulEquiv.toAdditive (MulAut.congr eW τ)).trans
      (prodCoordEquiv (K := K) (P := P)).symm))

@[simp] theorem coordinateAddEquiv_apply
    (eW : W ≃* (Multiplicative K × P)) (τ : MulAut W) (x : K) (p : Additive P) :
    coordinateAddEquiv eW τ (x, p) =
      ((eW (τ (eW.symm (Multiplicative.ofAdd x, p.toMul)))).1.toAdd,
        Additive.ofMul (eW (τ (eW.symm (Multiplicative.ofAdd x, p.toMul)))).2) := rfl


end Coordinate

section Root

variable {G : Type*} [Group G]
variable {W R P : Subgroup G}
variable {K : Type*} [Field K]


end Root


variable {F P : Type*} [Field F] [AddGroup P]


section GammaSemilinear

variable [Algebra (ZMod 2) F]


end GammaSemilinear

section GeneratedField

variable [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]


end GeneratedField


section PolynomialIntertwining

open Polynomial

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]


end PolynomialIntertwining


section RootFixedShears

variable {F P : Type*} [Field F] [CharP F 2] [Finite F]
  [AddGroup P] [Nontrivial P]


end RootFixedShears


section CoordinateComposition

variable {K P W : Type*} [Field K] [Group P] [Group W]


end CoordinateComposition

section TranslationCubes

variable {F P : Type*} [Field F] [CharP F 2] [Finite F]
  [AddGroup P] [Finite P]


end TranslationCubes


end CFSG.ScalarGraphAction

namespace CFSG.ScalarGraphAction

variable {V : Type*} [AddGroup V] [Finite V]
variable {A : Subgroup (Equiv.Perm V)}


end CFSG.ScalarGraphAction

namespace CFSG.ScalarGraphAction


end CFSG.ScalarGraphAction


namespace CFSG.ScalarGraphAction

open CFSG.ScalarGraphAction


variable {F P : Type*} [Field F] [CharP F 2] [Finite F]
  [AddGroup P] [Finite P]

@[expose]
def shearAdd (φ : P →+ F) (b : F) : AddAut (F × P) where
  toFun v := (v.1 + b * φ v.2, v.2)
  invFun v := (v.1 - b * φ v.2, v.2)
  left_inv v := by
    ext
    · simp only [sub_eq_add_neg]
      abel
    · rfl
  right_inv v := by
    ext
    · simp only [sub_eq_add_neg]
      abel
    · rfl
  map_add' u v := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add]
      rw [map_add, mul_add]
      abel
    · rfl

@[simp]
theorem shearAdd_apply (φ : P →+ F) (b : F) (r : F) (p : P) :
    shearAdd φ b (r, p) = (r + b * φ p, p) := rfl

@[simp]
theorem shearAdd_add_self (φ : P →+ F) (b : F) :
    shearAdd φ b + shearAdd φ b = 0 := by
  apply AddEquiv.ext
  intro v
  rcases v with ⟨r, p⟩
  have h2 : b * φ p + b * φ p = 0 := by
    rw [CharTwo.add_self_eq_zero]
  apply Prod.ext
  · simp [AddAut.add_apply, AddAut.zero_apply, shearAdd_apply, add_assoc, h2]
  · simp [AddAut.add_apply, AddAut.zero_apply, shearAdd_apply]

@[expose]
def shearAddHom (φ : P →+ F) : F →+ AddAut (F × P) where
  toFun := shearAdd φ
  map_zero' := by
    apply AddEquiv.ext
    intro v
    rcases v with ⟨r, p⟩
    apply Prod.ext
    · simp [shearAdd_apply]
    · simp [AddAut.zero_apply, shearAdd_apply]
  map_add' b c := by
    apply AddEquiv.ext
    intro v
    rcases v with ⟨r, p⟩
    apply Prod.ext
    · simp only [AddAut.add_apply, shearAdd_apply]
      change r + (b + c) * φ p = (r + c * φ p) + b * φ p
      rw [add_mul]
      abel
    · simp [AddAut.add_apply, shearAdd_apply]

@[simp]
theorem shearAdd_zero (φ : P →+ F) : shearAdd φ 0 = 0 :=
  (shearAddHom φ).map_zero


@[expose]
def shearSubgroup (φ : P →+ F) : Subgroup (Multiplicative (AddAut (F × P))) :=
  (shearAddHom φ).range.toSubgroup

@[simp]
theorem mem_shearSubgroup (φ : P →+ F) {x : Multiplicative (AddAut (F × P))} :
    x ∈ shearSubgroup φ ↔ ∃ b : F, x = Multiplicative.ofAdd (shearAdd φ b) := by
  rw [shearSubgroup, Multiplicative.mem_toSubgroup]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have hb' : Multiplicative.ofAdd (shearAdd φ b) = x := by
      simpa [shearAddHom] using congrArg Multiplicative.ofAdd hb
    exact hb'.symm
  · rintro ⟨b, rfl⟩
    exact ⟨b, rfl⟩


end CFSG.ScalarGraphAction

namespace CFSG.ScalarGraphAction


open scoped commutatorElement


end CFSG.ScalarGraphAction
