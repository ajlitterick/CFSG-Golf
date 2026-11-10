module

public import CFSG.LieType.AlgebraicGroups.PointedDerivation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Product

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TauCeti WithConv
open scoped TensorProduct

universe u v
variable {k : Type u} [CommRing k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H]


theorem derivationComp_mem_lieSubalgebra_of_stable
    (θ : H →ₐc[k] H) (I : HopfIdeal k H)
    (hs : ∀ a ∈ I.toIdeal, θ a ∈ I.toIdeal)
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k))
    (hd : d ∈ I.lieSubalgebra (B := k)) :
    derivationComp (B := k) θ d ∈ I.lieSubalgebra (B := k) := by
  rw [HopfIdeal.mem_lieSubalgebra_iff] at hd ⊢
  intro a ha
  rw [derivationComp_apply]
  exact hd (θ a) (hs a ha)


end CFSG.LieType.AlgebraicGroups
