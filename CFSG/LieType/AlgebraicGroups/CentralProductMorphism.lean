module

public import CFSG.LieType.AlgebraicGroups.FixedComponentProduct
public import CFSG.LieType.AlgebraicGroups.G2ExceptionalComorphism
public import TauCeti.RingTheory.FiniteType.Tensor.Product
public import TauCeti.RingTheory.TensorProduct.PointSeparation
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.Finite
public import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Points
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer

public noncomputable section

open CategoryTheory WithConv
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.CentralProduct

open CFSG.LieType.AlgebraicGroups

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose] def centralProductAlgHom
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) : M →ₐ[k] (T ⊗[k] D) :=
  (Algebra.TensorProduct.map (iT : M →ₐ[k] T) (iD : M →ₐ[k] D)).comp
    (Bialgebra.comulAlgHom k M)

@[expose] def PointImageCentral
    {M T : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k} (iT : M →ₐc[k] T) : Prop :=
  ∀ (A : CommAlgCat.{u} k) (t : TauCeti.HopfAlgebra.points (R := k) (H := T) A),
    TauCeti.HopfAlgebra.IsCentralPoint (TauCeti.AlgHom.mapDomain iT t)


omit [IsAlgClosed k] in
theorem pointImage_commute
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    (A : CommAlgCat.{u} k) (t : TauCeti.HopfAlgebra.points (R := k) (H := T) A)
    (d : TauCeti.HopfAlgebra.points (R := k) (H := D) A) :
    Commute (TauCeti.AlgHom.mapDomain iT t) (TauCeti.AlgHom.mapDomain iD d) :=
  (hT A t).commute (TauCeti.AlgHom.mapDomain iD d)

omit [IsAlgClosed k] in
theorem centralProductAlgHom_point_eq
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D)
    (A : CommAlgCat.{u} k)
    (y : TauCeti.HopfAlgebra.points (R := k) (H := T ⊗[k] D) A) :
    toConv (y.ofConv.comp (centralProductAlgHom (k := k) iT iD)) =
      TauCeti.AlgHom.mapDomain iT
          (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (A := A) y).1 *
        TauCeti.AlgHom.mapDomain iD
          (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (A := A) y).2 := by
  let phi : (M ⊗[k] M) →ₐ[k] A :=
    y.ofConv.comp (Algebra.TensorProduct.map (iT : M →ₐ[k] T) (iD : M →ₐ[k] D))
  have hraw := TauCeti.Bialgebra.toConv_comp_comulAlgHom (R := k) (H := M) (A := A)
    (phi := phi)
  have hleft : phi.comp
      (TauCeti.Bialgebra.TensorProduct.includeLeft (R := k) (H₁ := M) (H₂ := M)).toAlgHom =
      (y.ofConv.comp
        (TauCeti.Bialgebra.TensorProduct.includeLeft (R := k) (H₁ := T) (H₂ := D)).toAlgHom).comp
        (iT : M →ₐ[k] T) := by
    dsimp only [phi]
    simp only [TauCeti.Bialgebra.TensorProduct.includeLeft_toAlgHom]
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft, ← AlgHom.comp_assoc]
  have hright : phi.comp
      (TauCeti.Bialgebra.TensorProduct.includeRight (R := k) (H₁ := M) (H₂ := M)).toAlgHom =
      (y.ofConv.comp
        (TauCeti.Bialgebra.TensorProduct.includeRight (R := k) (H₁ := T) (H₂ := D)).toAlgHom).comp
        (iD : M →ₐ[k] D) := by
    dsimp only [phi]
    simp only [TauCeti.Bialgebra.TensorProduct.includeRight_toAlgHom]
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeRight, ← AlgHom.comp_assoc]
  have hfst : (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (A := A) y).1 =
      toConv (y.ofConv.comp
        (TauCeti.Bialgebra.TensorProduct.includeLeft (R := k) (H₁ := T) (H₂ := D)).toAlgHom) := by
    rw [TauCeti.AffineGroup.Product.pointsMulEquiv_apply, TauCeti.AlgHom.mapDomain_apply]
  have hsnd : (TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (A := A) y).2 =
      toConv (y.ofConv.comp
        (TauCeti.Bialgebra.TensorProduct.includeRight (R := k) (H₁ := T) (H₂ := D)).toAlgHom) := by
    rw [TauCeti.AffineGroup.Product.pointsMulEquiv_apply, TauCeti.AlgHom.mapDomain_apply]
    rfl
  change toConv (phi.comp (Bialgebra.comulAlgHom k M)) = _
  rw [hraw, hleft, hright, hfst, hsnd]
  rfl

omit [IsAlgClosed k] in
theorem centralProductAlgHom_point_mul
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    (y z : WithConv ((T ⊗[k] D) →ₐ[k] k)) :
    toConv ((y * z).ofConv.comp (centralProductAlgHom (k := k) iT iD)) =
      toConv (y.ofConv.comp (centralProductAlgHom (k := k) iT iD)) *
        toConv (z.ofConv.comp (centralProductAlgHom (k := k) iT iD)) := by
  let A := CommAlgCat.of k k
  let P := TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (A := A)
    (H₁ := T) (H₂ := D)
  have hy := centralProductAlgHom_point_eq (k := k) iT iD A y
  have hz := centralProductAlgHom_point_eq (k := k) iT iD A z
  have hyz := centralProductAlgHom_point_eq (k := k) iT iD A (y * z)
  have hcomp : P (y * z) = P y * P z := map_mul P y z
  have hfst : (P (y * z)).1 = (P y).1 * (P z).1 := by
    rw [hcomp]
    rfl
  have hsnd : (P (y * z)).2 = (P y).2 * (P z).2 := by
    rw [hcomp]
    rfl
  have hcomm : Commute (TauCeti.AlgHom.mapDomain iT (P z).1)
      (TauCeti.AlgHom.mapDomain iD (P y).2) :=
    pointImage_commute (k := k) iT iD hT A (P z).1 (P y).2
  calc
    toConv ((y * z).ofConv.comp (centralProductAlgHom (k := k) iT iD)) =
        TauCeti.AlgHom.mapDomain iT (P (y * z)).1 *
          TauCeti.AlgHom.mapDomain iD (P (y * z)).2 := hyz
    _ = TauCeti.AlgHom.mapDomain iT ((P y).1 * (P z).1) *
          TauCeti.AlgHom.mapDomain iD ((P y).2 * (P z).2) := by rw [hfst, hsnd]
    _ = (TauCeti.AlgHom.mapDomain iT (P y).1 * TauCeti.AlgHom.mapDomain iT (P z).1) *
          (TauCeti.AlgHom.mapDomain iD (P y).2 * TauCeti.AlgHom.mapDomain iD (P z).2) := by
      rw [map_mul, map_mul]
    _ = (TauCeti.AlgHom.mapDomain iT (P y).1 * TauCeti.AlgHom.mapDomain iD (P y).2) *
          (TauCeti.AlgHom.mapDomain iT (P z).1 * TauCeti.AlgHom.mapDomain iD (P z).2) := by
      calc
        (TauCeti.AlgHom.mapDomain iT (P y).1 * TauCeti.AlgHom.mapDomain iT (P z).1) *
            (TauCeti.AlgHom.mapDomain iD (P y).2 * TauCeti.AlgHom.mapDomain iD (P z).2) =
          TauCeti.AlgHom.mapDomain iT (P y).1 *
            ((TauCeti.AlgHom.mapDomain iT (P z).1 *
              TauCeti.AlgHom.mapDomain iD (P y).2) *
              TauCeti.AlgHom.mapDomain iD (P z).2) := by rw [mul_assoc, mul_assoc]
        _ = TauCeti.AlgHom.mapDomain iT (P y).1 *
            ((TauCeti.AlgHom.mapDomain iD (P y).2 *
              TauCeti.AlgHom.mapDomain iT (P z).1) *
              TauCeti.AlgHom.mapDomain iD (P z).2) := by rw [hcomm.eq]
        _ = (TauCeti.AlgHom.mapDomain iT (P y).1 * TauCeti.AlgHom.mapDomain iD (P y).2) *
            (TauCeti.AlgHom.mapDomain iT (P z).1 * TauCeti.AlgHom.mapDomain iD (P z).2) := by
          rw [mul_assoc, mul_assoc]
    _ = toConv (y.ofConv.comp (centralProductAlgHom (k := k) iT iD)) *
          toConv (z.ofConv.comp (centralProductAlgHom (k := k) iT iD)) := by rw [hy, hz]

@[expose] def centralProductBialgHom
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D] : M →ₐc[k] (T ⊗[k] D) :=
  letI : Algebra.FiniteType k (T ⊗[k] D) :=
    TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct_finiteType (R := k) T D
  haveI : IsReduced (T ⊗[k] D) := inferInstance
  bialgHomOfPointMulTo (centralProductAlgHom (k := k) iT iD)
    (centralProductAlgHom_point_mul (k := k) iT iD hT)

@[simp] theorem coe_centralProductBialgHom
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D] :
    (centralProductBialgHom (k := k) iT iD hT : M →ₐ[k] (T ⊗[k] D)) =
      centralProductAlgHom (k := k) iT iD := by
  rfl

@[expose] def centralProductHom
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D] :
    M ⟶ TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T D :=
  TauCeti.FiniteTypeCommHopfAlgCat.ofHom (centralProductBialgHom (k := k) iT iD hT)

@[simp] theorem toBialgHom_centralProductHom
    {M T D : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}
    (iT : M →ₐc[k] T) (iD : M →ₐc[k] D) (hT : PointImageCentral iT)
    [IsReduced T] [IsReduced D] :
    TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (centralProductHom (k := k) iT iD hT) =
      centralProductBialgHom (k := k) iT iD hT :=
  rfl


end CFSG.LieType.AlgebraicGroups.CentralProduct
