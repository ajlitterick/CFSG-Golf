module

public import CFSG.Monster.B.Gen.MinkowskiTwo
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Monster.B.OddDegree

open Module Matrix

variable {G : Type*} [Group G] {n : ℕ} (ρ : G →* GL (Fin n) ℚ)

@[expose] noncomputable def lat : Submodule ℤ (Fin n → ℚ) :=
  Submodule.span ℤ (Set.range fun p : G × Fin n =>
    (ρ p.1 : Matrix (Fin n) (Fin n) ℚ) *ᵥ Pi.single p.2 1)


variable [Finite G]

instance : Module.Finite ℤ (lat ρ) := by
  have : Finite (G × Fin n) := inferInstance
  exact Module.Finite.span_of_finite ℤ (Set.finite_range _)

instance : Module.Free ℤ (lat ρ) := Module.free_of_finite_type_torsion_free'


end CFSG.Monster.B.OddDegree
