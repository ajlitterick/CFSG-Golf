module

public import CFSG.LieType.AlgebraicGroups.ImagePointsOpen
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import CFSG.LieType.AlgebraicGroups.ClosedCone

public noncomputable section

open WithConv TauCeti.Comodule
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u v w

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable {M : Type w} [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M]

variable (k H) in
@[expose] def orbitCone (v : M) : Set M :=
  {w | ∃ g : WithConv (H →ₐ[k] k), ∃ c : k, w = c • basePointsRepresentation (H := H) M g v}

variable (H) in
@[expose] def orbitComap {n : ℕ} (b : Module.Basis (Fin n) k M) (v : M) :
    MvPolynomial (Fin n) k →ₐ[k] H ⊗[k] Polynomial k :=
  MvPolynomial.aeval fun i => matrixCoefficient (C := H) (b.coord i) v ⊗ₜ Polynomial.X

theorem comp_orbitComap {n : ℕ} (b : Module.Basis (Fin n) k M) (v : M)
    (z : H ⊗[k] Polynomial k →ₐ[k] k) :
    z.comp (orbitComap H b v) = MvPolynomial.aeval (b.equivFun
      (z (1 ⊗ₜ Polynomial.X) • basePointsRepresentation (H := H) M
        (toConv (z.comp Algebra.TensorProduct.includeLeft)) v)) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, orbitComap, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
    show matrixCoefficient (C := H) (b.coord i) v ⊗ₜ[k] Polynomial.X =
      (matrixCoefficient (C := H) (b.coord i) v ⊗ₜ[k] (1 : Polynomial k)) *
        ((1 : H) ⊗ₜ Polynomial.X) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul,
    show z (matrixCoefficient (C := H) (b.coord i) v ⊗ₜ[k] (1 : Polynomial k)) =
      (toConv (z.comp Algebra.TensorProduct.includeLeft)).ofConv
        (matrixCoefficient (C := H) (b.coord i) v) from rfl,
    apply_matrixCoefficient]
  simp [Module.Basis.equivFun_apply, Module.Basis.coord_apply, mul_comm]

@[expose] def tensorPoint (g : WithConv (H →ₐ[k] k)) (c : k) : H ⊗[k] Polynomial k →ₐ[k] k :=
  Algebra.TensorProduct.lift g.ofConv (Polynomial.aeval c) fun _ _ => Commute.all _ _

theorem tensorPoint_X (g : WithConv (H →ₐ[k] k)) (c : k) :
    tensorPoint g c (1 ⊗ₜ Polynomial.X) = c := by
  simp [tensorPoint]

theorem tensorPoint_comp_includeLeft (g : WithConv (H →ₐ[k] k)) (c : k) :
    toConv ((tensorPoint g c).comp Algebra.TensorProduct.includeLeft) = g := by
  ext x
  simp [tensorPoint]

theorem mem_orbitCone_iff {n : ℕ} (b : Module.Basis (Fin n) k M) (v w : M) :
    w ∈ orbitCone k H v ↔ ∃ z : H ⊗[k] Polynomial k →ₐ[k] k,
      z.comp (orbitComap H b v) = MvPolynomial.aeval (b.equivFun w) := by
  constructor
  · rintro ⟨g, c, rfl⟩
    refine ⟨tensorPoint g c, ?_⟩
    rw [comp_orbitComap, tensorPoint_X, tensorPoint_comp_includeLeft]
  · rintro ⟨z, hz⟩
    refine ⟨toConv (z.comp Algebra.TensorProduct.includeLeft), z (1 ⊗ₜ Polynomial.X), ?_⟩
    rw [comp_orbitComap] at hz
    refine b.equivFun.injective (funext fun i => ?_)
    have := congrArg (fun f : MvPolynomial (Fin n) k →ₐ[k] k => f (MvPolynomial.X i)) hz
    simpa using this.symm

variable (H) in
@[expose] def orbitClosure {n : ℕ} (b : Module.Basis (Fin n) k M) (v : M) : Set M :=
  b.equivFun ⁻¹' MvPolynomial.zeroLocus k (RingHom.ker (orbitComap H b v))

theorem isZariskiClosed_orbitClosure {n : ℕ} (b : Module.Basis (Fin n) k M) (v : M) :
    IsZariskiClosed k (orbitClosure H b v) :=
  isZariskiClosed_preimage_zeroLocus b _

theorem orbitCone_subset_orbitClosure {n : ℕ} (b : Module.Basis (Fin n) k M) (v : M) :
    orbitCone k H v ⊆ orbitClosure H b v := by
  intro w hw
  obtain ⟨z, hz⟩ := (mem_orbitCone_iff b v w).mp hw
  rw [orbitClosure, Set.mem_preimage, MvPolynomial.mem_zeroLocus_iff]
  intro p hp
  rw [← hz, AlgHom.comp_apply, RingHom.mem_ker.mp hp, map_zero]

section Domain

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]

instance isDomain_tensorPolynomial : IsDomain (H ⊗[k] Polynomial k) :=
  Function.Injective.isDomain ((polyEquivTensor k H).symm : H ⊗[k] Polynomial k →+* Polynomial H)
    (polyEquivTensor k H).symm.injective

instance finiteType_tensorPolynomial : Algebra.FiniteType k (H ⊗[k] Polynomial k) :=
  Algebra.FiniteType.equiv (Algebra.FiniteType.trans (S := H) inferInstance inferInstance)
    (polyEquivTensor k H)

theorem mem_ker_orbitComap {n : ℕ} (b : Module.Basis (Fin n) k M) (v : M)
    {p : MvPolynomial (Fin n) k}
    (hp : ∀ w ∈ orbitCone k H v, MvPolynomial.aeval (b.equivFun w) p = 0) :
    p ∈ RingHom.ker (orbitComap H b v) := by
  rw [RingHom.mem_ker]
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro z
  rw [map_zero, ← AlgHom.comp_apply, comp_orbitComap]
  exact hp _ ⟨_, _, rfl⟩

theorem orbitClosure_subset {n : ℕ} (b : Module.Basis (Fin n) k M) (v : M) {Z : Set M}
    (hZ : IsZariskiClosed k Z) (hvZ : orbitCone k H v ⊆ Z) : orbitClosure H b v ⊆ Z := by
  obtain ⟨J, rfl⟩ := hZ.exists_eq_preimage_zeroLocus b
  refine Set.preimage_mono (MvPolynomial.zeroLocus_anti_mono fun p hp => ?_)
  exact mem_ker_orbitComap b v fun w hw =>
    (MvPolynomial.mem_zeroLocus_iff.mp (hvZ hw)) p hp

theorem basePointsRepresentation_mem_orbitClosure {n : ℕ} (b : Module.Basis (Fin n) k M)
    (v : M) (h : WithConv (H →ₐ[k] k)) {w : M} (hw : w ∈ orbitClosure H b v) :
    basePointsRepresentation (H := H) M h w ∈ orbitClosure H b v := by
  have hsub : orbitClosure H b v ⊆
      (basePointsRepresentation (H := H) M h : M →ₗ[k] M) ⁻¹' orbitClosure H b v := by
    refine orbitClosure_subset b v ((isZariskiClosed_orbitClosure b v).preimage _) ?_
    rintro _ ⟨g, c, rfl⟩
    refine orbitCone_subset_orbitClosure b v ⟨h * g, c, ?_⟩
    simp [map_mul, Module.End.mul_apply]
  exact hsub hw

theorem isCone_orbitClosure {n : ℕ} (b : Module.Basis (Fin n) k M) (v : M) :
    IsCone k (orbitClosure H b v) := by
  intro t w hw
  have hsub : orbitClosure H b v ⊆ (t • LinearMap.id : M →ₗ[k] M) ⁻¹' orbitClosure H b v := by
    refine orbitClosure_subset b v ((isZariskiClosed_orbitClosure b v).preimage _) ?_
    rintro _ ⟨g, c, rfl⟩
    exact orbitCone_subset_orbitClosure b v ⟨g, t * c, by simp [smul_smul, mul_comm]⟩
  exact hsub hw

theorem ker_orbitComap_le_of_mem_orbitClosure {n : ℕ} (b : Module.Basis (Fin n) k M) {v w : M}
    (hw : w ∈ orbitClosure H b v) :
    RingHom.ker (orbitComap H b v) ≤ RingHom.ker (orbitComap H b w) := by
  intro p hp
  refine mem_ker_orbitComap b w fun x hx => ?_
  obtain ⟨g, c, rfl⟩ := hx
  have hmem : c • basePointsRepresentation (H := H) M g w ∈ orbitClosure H b v :=
    isCone_orbitClosure b v c _ (basePointsRepresentation_mem_orbitClosure b v g hw)
  exact (MvPolynomial.mem_zeroLocus_iff.mp hmem) p hp


end Domain

end CFSG.LieType.AlgebraicGroups.ClosedCone
