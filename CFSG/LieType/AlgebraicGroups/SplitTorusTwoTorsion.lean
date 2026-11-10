module

public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import CFSG.LieType.AlgebraicGroups.TorusCoordinates
public import CFSG.LieType.AlgebraicGroups.TangentSpace
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.Mathlib.RingTheory.UnitOrderOf
public import CFSG.Mathlib.RingTheory.RootsOfUnity.ZModUnits

import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
import TauCeti.RingTheory.RootsOfUnity.ZMod
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Data.ZMod.Basic

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open WithConv

open scoped CFSG.ConvolutionPoints

open CategoryTheory

variable {L : Type} [Field L] [IsAlgClosed L] {R : Type} [CommRing R] [HopfAlgebra L R]
  [Algebra.FiniteType L R]

section TangentMonoidAlgebra

variable {σ : Type} [Fintype σ]

private def exponent (c : σ → L) (m : Multiplicative (σ →₀ ℤ)) : L :=
  (Multiplicative.toAdd m).sum fun i e => e • c i


end TangentMonoidAlgebra


section PrimeTorsion

private noncomputable def sign (p : ℕ) [NeZero p] (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    Multiplicative (Fin n → ZMod p) →* (ULift (Fin n) → Lˣ) where
  toFun x := fun i => (zmodToUnits (L := L) p ζ hζ (x.toAdd i.down)).toMul
  map_one' := by
    funext i
    simp [zmodToUnits]
  map_mul' x y := by
    funext i
    simp only [toAdd_mul, Pi.add_apply, Pi.mul_apply, map_add, toMul_add]


end PrimeTorsion


end CFSG.LieType.AlgebraicGroups

end
