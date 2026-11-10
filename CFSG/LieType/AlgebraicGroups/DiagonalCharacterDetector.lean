module

public import CFSG.LieType.AlgebraicGroups.TorusCoordinates
public import CFSG.LieType.AlgebraicGroups.EquivariantAffineEmbedding
public import CFSG.LinearAlgebra.TorusPrimeTorsion
public import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation

public noncomputable section

open CategoryTheory WithConv TauCeti
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

def diagonalCharacterHom
    (T : FiniteTypeCommHopfAlgCat.{u,u} k) {n : ℕ}
    (c : Fin n → _root_.GroupLike k T) :
    WithConv (T →ₐ[k] k) →* (Fin n → kˣ) := by
  let E := DiagonalizableGroup.pointsMulEquiv
    (R := k) (G := _root_.GroupLike k T) (A := k)
  let a := TauCeti.GroupLike.evaluationBialgHom k T
  exact
    { toFun := fun t i => E (AlgHom.mapDomain a t) (c i)
      map_one' := by
        have h : E (AlgHom.mapDomain a (1 : WithConv (T →ₐ[k] k))) = 1 := by
          rw [map_one, map_one]
        exact congrArg (fun χ => fun i => χ (c i)) h
      map_mul' := by
        intro t s
        have h : E (AlgHom.mapDomain a (t * s)) =
            E (AlgHom.mapDomain a t) * E (AlgHom.mapDomain a s) := by
          rw [map_mul, map_mul]
        exact congrArg (fun χ => fun i => χ (c i)) h }

omit [IsAlgClosed k] in
@[simp] theorem diagonalCharacterHom_apply_val
    (T : FiniteTypeCommHopfAlgCat.{u,u} k) {n : ℕ}
    (c : Fin n → _root_.GroupLike k T)
    (t : WithConv (T →ₐ[k] k)) (i : Fin n) :
    (diagonalCharacterHom T c t i : k) = t.ofConv (c i) := by
  let a := TauCeti.GroupLike.evaluationBialgHom k T
  change ((DiagonalizableGroup.pointsMulEquiv (AlgHom.mapDomain a t)) (c i) : k) = _
  rw [DiagonalizableGroup.pointsMulEquiv_apply, DiagonalizableGroup.charOfPoint_apply_coe]
  rw [AlgHom.mapDomain_apply]
  change t.ofConv (a (MonoidAlgebra.single (c i) 1)) = t.ofConv (c i)
  rw [TauCeti.GroupLike.evaluationBialgHom_single, one_smul]


end CFSG.LieType.AlgebraicGroups
