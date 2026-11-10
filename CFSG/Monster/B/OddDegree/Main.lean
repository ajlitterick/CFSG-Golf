module

public import CFSG.Monster.B.OddDegree.Section
public import CFSG.Monster.B.OddDegree.Lattice
public import CFSG.Monster.B.OddDegree.Form
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Polynomial.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.OddDegree

open Module Matrix

section Section

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : G →* Module.End (ZMod 2) W) {U' U : Submodule (ZMod 2) W} (hU' : Invariant ρ U')
  (hU : Invariant ρ U)

@[expose] noncomputable def secEnd (g : G) :
    Module.End (ZMod 2) (U ⧸ U'.comap U.subtype) :=
  (U'.comap U.subtype).mapQ (U'.comap U.subtype) ((ρ g).restrict (hU g))
    (fun x hx => hU' g x hx)

theorem secEnd_mk (g : G) (u : U) :
    secEnd ρ hU' hU g (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ⟨ρ g u, hU g u u.2⟩ := rfl

@[expose] noncomputable def secRep : G →* Module.End (ZMod 2) (U ⧸ U'.comap U.subtype) where
  toFun := secEnd ρ hU' hU
  map_one' := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H u =>
      rw [secEnd_mk, Module.End.one_apply]
      congr 1
      apply Subtype.ext
      show (ρ 1) (u : W) = u
      rw [map_one, Module.End.one_apply]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H u =>
      rw [Module.End.mul_apply, secEnd_mk, secEnd_mk, secEnd_mk]
      congr 1
      apply Subtype.ext
      show (ρ (g * h)) (u : W) = (ρ g) ((ρ h) u)
      rw [map_mul, Module.End.mul_apply]


theorem finrank_sec [FiniteDimensional (ZMod 2) W] (hle : U' ≤ U) :
    finrank (ZMod 2) (U ⧸ U'.comap U.subtype) = finrank (ZMod 2) U - finrank (ZMod 2) U' := by
  have h := Submodule.finrank_quotient_add_finrank (U'.comap U.subtype)
  have h2 : finrank (ZMod 2) (U'.comap U.subtype) = finrank (ZMod 2) U' :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)
  omega


end Section

section Matrices

variable {G Q : Type*} [Group G] [AddCommGroup Q] [Module (ZMod 2) Q] {d : ℕ}
  (b : Module.Basis (Fin d) (ZMod 2) Q) (σ : G →* Module.End (ZMod 2) Q)

@[expose] noncomputable def matRep : G →* GL (Fin d) (ZMod 2) :=
  ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp σ).toHomUnits


end Matrices

section Padding


end Padding

section Generic


end Generic


end CFSG.Monster.B.OddDegree
