module

public import CFSG.LieType.AlgebraicGroups.CentralizerUnipotentFixed

public noncomputable section

open WithConv TauCeti.Comodule
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.CartanComponent

universe u

variable {k : Type u} [Field k]

section LinearAlgebra

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]


end LinearAlgebra

section Regular

variable {M : Type u} [CommRing M] [HopfAlgebra k M]
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]
  [FiniteDimensional k W]


theorem exists_apply_eq_coeff_charpoly :
    ∃ c : ℕ → M, ∀ (g : WithConv (M →ₐ[k] k)) (i : ℕ),
      g.ofConv (c i) = (LinearMap.charpoly (basePointsRepresentation (H := M) W g)).coeff i := by
  classical
  let b := Module.finBasis k W
  let A : Matrix (Fin (Module.finrank k W)) (Fin (Module.finrank k W)) M := Matrix.of fun a j =>
    matrixCoefficient (C := M) (b.coord a) (b j)
  refine ⟨fun i => A.charpoly.coeff i, fun g i => ?_⟩
  have hA : A.map g.ofConv = LinearMap.toMatrix b b (basePointsRepresentation (H := M) W g) := by
    ext a j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply]
    change g.ofConv (matrixCoefficient (C := M) (b.coord a) (b j)) = _
    rw [apply_matrixCoefficient]
    rfl
  rw [← LinearMap.charpoly_toMatrix _ b, ← hA,
    show A.map g.ofConv = A.map (g.ofConv : M →+* k) from rfl, Matrix.charpoly_map,
    Polynomial.coeff_map]
  rfl

end Regular

section Points


end Points

section Weights


end Weights

section Unipotence


end Unipotence

section Cartan


end Cartan

end CFSG.LieType.AlgebraicGroups.CartanComponent
