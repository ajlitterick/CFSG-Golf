module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthEigen
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

namespace CFSG.ClassicalInvolution.ModelFacts.MF15

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

structure SemiSim (Q : QuadraticForm F V) where
  toFun : V → V
  φ : F ≃+* F
  μ : F
  μ_ne : μ ≠ 0
  map_add' : ∀ v w, toFun (v + w) = toFun v + toFun w
  map_smul' : ∀ (c : F) (v : V), toFun (c • v) = φ c • toFun v
  bijective : Function.Bijective toFun
  map_Q' : ∀ v, Q (toFun v) = μ * φ (Q v)

namespace SemiSim

variable {Q : QuadraticForm F V}


end SemiSim


@[expose] def SignPlus (Q : QuadraticForm F V) (U : Submodule F V) : Prop :=
  CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict U)


open scoped Classical in
@[expose] noncomputable def piSign (F : Type) [Field F] : Bool := decide (IsSquare (-1 : F))


end CFSG.ClassicalInvolution.ModelFacts.MF15
