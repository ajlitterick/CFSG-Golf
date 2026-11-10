module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
public import CFSG.ThirdParty.TauCeti.HopfIdealNormalRationalPoint
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.HopkinsLevitzki

public noncomputable section

open WithConv
open CategoryTheory
open scoped TensorProduct

universe u

namespace CFSG.LieType.AlgebraicGroups.ReductiveDescent

variable {k : Type u} [Field k] [IsAlgClosed k]


noncomputable local instance componentGroupPointsGroup
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    Group ↑(TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints H) :=
  (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints H).str


end CFSG.LieType.AlgebraicGroups.ReductiveDescent
