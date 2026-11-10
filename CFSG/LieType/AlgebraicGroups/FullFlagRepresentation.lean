module

public import CFSG.LieType.AlgebraicGroups.FullFlagCone
public import CFSG.LieType.AlgebraicGroups.ChevalleyLine

public noncomputable section

open WithConv TauCeti.Comodule
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u

variable {k H V : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable [AddCommGroup V] [Module k V] [TauCeti.Comodule k H V]

attribute [local instance] TauCeti.Comodule.exteriorAlgebra TauCeti.Comodule.tensor

@[expose] def exteriorPowerData (r : ℕ) :
    Σ c : TauCeti.Comodule k H (⋀[k]^r V),
      letI := c
      {f : TauCeti.Comodule.Hom k H (⋀[k]^r V) (ExteriorAlgebra k V) //
        f.toLinearMap = (⋀[k]^r V).subtype} := by
  rw [← exteriorPowerSubcomodule_toSubmodule (R := k) (H := H) (M := V) r]
  exact ⟨TauCeti.Subcomodule.instComodule (N := exteriorPowerSubcomodule k H V r),
    ⟨(exteriorPowerSubcomodule k H V r).subtype, by
      rw [TauCeti.Subcomodule.subtype_toLinearMap]
      ext p
      change (p : ExteriorAlgebra k V) = (p : ExteriorAlgebra k V)
      rfl⟩⟩

@[expose, instance_reducible] def exteriorPowerComodule (r : ℕ) :
    TauCeti.Comodule k H (⋀[k]^r V) :=
  (exteriorPowerData (H := H) (V := V) r).1

attribute [local instance] exteriorPowerComodule


instance flagTensorComodule : (r : ℕ) → TauCeti.Comodule k H (FlagTensor k V r)
  | 0 => TauCeti.Comodule.trivial
  | r + 1 => by
    letI := flagTensorComodule r
    exact inferInstanceAs (TauCeti.Comodule k H
      (FlagTensor k V r ⊗[k] (⋀[k]^(r + 1) V)))


end CFSG.LieType.AlgebraicGroups.ClosedCone
