module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.Quasithin.RonanG51

open scoped TensorProduct Matrix

variable (F : Type) [Field F] [Algebra (ZMod 2) F] {V : Type} [AddCommGroup V]
  [Module (ZMod 2) V] {n : ℕ} (e : V ≃ₗ[ZMod 2] (Fin n → ZMod 2))

noncomputable def theta : (F ⊗[ZMod 2] V) ≃ₗ[F] (Fin n → F) :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl F F) e).trans
    (TensorProduct.piScalarRight (ZMod 2) F F (Fin n))


end CFSG.Quasithin.RonanG51
