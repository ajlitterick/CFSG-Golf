module

public import CFSG.LinearAlgebra.ExteriorIncidence
public import CFSG.LieType.AlgebraicGroups.ClosedOrbitFixed

public noncomputable section

open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u w

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

@[expose, reducible] def flagModule (k V : Type u) [Field k] [AddCommGroup V] [Module k V] :
    ℕ → ModuleCat k
  | 0 => ModuleCat.of k k
  | r + 1 => ModuleCat.of k (flagModule k V r ⊗[k] (⋀[k]^(r + 1) V))

abbrev FlagTensor (k V : Type u) [Field k] [AddCommGroup V] [Module k V] (r : ℕ) : Type u :=
  flagModule k V r

instance flagTensorFiniteDimensional [FiniteDimensional k V] :
    (r : ℕ) → FiniteDimensional k (FlagTensor k V r)
  | 0 => inferInstance
  | r + 1 => by
    let := flagTensorFiniteDimensional r
    exact inferInstanceAs (FiniteDimensional k
      (FlagTensor k V r ⊗[k] (⋀[k]^(r + 1) V)))

variable {I : Type w} [Fintype I]


def firstIndices (d r : ℕ) : Finset (Fin d) := Finset.univ.filter fun i => i.val < r

@[simp] theorem mem_firstIndices {d r : ℕ} (i : Fin d) :
    i ∈ firstIndices d r ↔ i.val < r := by
  simp [firstIndices]


end CFSG.LieType.AlgebraicGroups.ClosedCone
