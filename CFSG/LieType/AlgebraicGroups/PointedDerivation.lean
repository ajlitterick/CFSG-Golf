module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap

public noncomputable section

namespace Derivation

open TauCeti

universe u v w
variable {R : Type u} [CommRing R]
section Bialgebra

variable {H : Type v} [CommRing H] [Bialgebra R H]
variable {A : Type w} [CommRing A] [Bialgebra R A]

private def compCounitAux (f : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A R)) :
    Derivation R H (Bialgebra.CounitAlgebra R H R) := by
  let eA := Bialgebra.CounitAlgebra.algEquivSelf R A R
  let eH := Bialgebra.CounitAlgebra.algEquivSelf R H R
  let θ := eA.toLinearEquiv.trans eH.symm.toLinearEquiv
  refine Derivation.mk' (θ.toLinearMap.comp
    ((d : A →ₗ[R] Bialgebra.CounitAlgebra R A R).comp f.toLinearMap)) ?_
  intro a b
  have ha := DFunLike.congr_fun hf a
  have hb := DFunLike.congr_fun hf b
  simp only [AlgHom.comp_apply, _root_.Bialgebra.counitAlgHom_apply] at ha hb
  apply eH.injective
  change eH (eH.symm (eA (d (f (a * b))))) =
    eH (a • eH.symm (eA (d (f b))) + b • eH.symm (eA (d (f a))))
  rw [AlgEquiv.apply_symm_apply, map_add]
  dsimp only [eA, eH]
  simp only [Bialgebra.CounitAlgebra.algEquivSelf_smul,
    AlgEquiv.apply_symm_apply]
  rw [map_mul, Bialgebra.CounitAlgebra.algEquivSelf_apply_mul]
  simp only [ha, hb]

private theorem compCounitAux_apply (f : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A R)) (a : H) :
    compCounitAux f hf d a =
      (Bialgebra.CounitAlgebra.algEquivSelf R H R).symm
        (Bialgebra.CounitAlgebra.algEquivSelf R A R (d (f a))) := by
  rfl

def compCounit (f : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H) :
    Derivation R A (Bialgebra.CounitAlgebra R A R) →ₗ[R]
      Derivation R H (Bialgebra.CounitAlgebra R H R) where
  toFun := compCounitAux f hf
  map_add' d e := by
    ext a
    simp only [compCounitAux_apply, Derivation.add_apply, map_add]
  map_smul' r d := by
    ext a
    apply (Bialgebra.CounitAlgebra.algEquivSelf R H R).injective
    rw [compCounitAux_apply, AlgEquiv.apply_symm_apply,
      algEquivSelf_derivation_smul_apply, algEquivSelf_derivation_smul_apply,
      compCounitAux_apply, AlgEquiv.apply_symm_apply]
    simp only [RingHom.id_apply]

@[simp] theorem compCounit_apply (f : H →ₐ[R] A)
    (hf : (_root_.Bialgebra.counitAlgHom R A).comp f =
      _root_.Bialgebra.counitAlgHom R H)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A R)) (a : H) :
    compCounit f hf d a =
      (Bialgebra.CounitAlgebra.algEquivSelf R H R).symm
        (Bialgebra.CounitAlgebra.algEquivSelf R A R (d (f a))) :=
  compCounitAux_apply f hf d a


end Bialgebra

section Hopf

open _root_.Coalgebra TensorProduct WithConv


end Hopf

end Derivation
