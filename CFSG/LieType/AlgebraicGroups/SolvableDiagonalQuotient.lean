module

public import CFSG.LieType.AlgebraicGroups.TorusTriangularRepresentation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
public import TauCeti.Algebra.Bialgebra.GroupLike.Torsion
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Character
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public noncomputable section

open CategoryTheory WithConv TauCeti
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]


def triangularDiagonalCharacterMap
    (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hdiag : ∀ i, IsGroupLikeElem k (Comodule.coefficientMatrix (C := H) b i i)) :
    MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐc[k] H :=
  (TauCeti.GroupLike.evaluationBialgHom k H).comp
    (MonoidAlgebra.mapDomainBialgHom k
      (TauCeti.freeAbelianCharEquiv.symm
        (fun i : ULift.{u} (Fin n) => (⟨Comodule.coefficientMatrix (C := H) b i.down i.down,
          hdiag i.down⟩ : _root_.GroupLike k H))))

omit [IsAlgClosed k] in
@[simp] theorem triangularDiagonalCharacterMap_single
    (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hdiag : ∀ i, IsGroupLikeElem k (Comodule.coefficientMatrix (C := H) b i i))
    (i : Fin n) :
    triangularDiagonalCharacterMap H b hdiag
      (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1) =
        Comodule.coefficientMatrix (C := H) b i i := by
  simp only [triangularDiagonalCharacterMap, BialgHom.comp_apply,
    MonoidAlgebra.mapDomainBialgHom_single,
    TauCeti.freeAbelianCharEquiv_symm_apply_ofAdd_single,
    TauCeti.GroupLike.evaluationBialgHom_single, one_smul]


end CFSG.LieType.AlgebraicGroups
