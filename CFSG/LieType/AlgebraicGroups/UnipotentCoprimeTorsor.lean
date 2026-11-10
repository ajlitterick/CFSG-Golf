module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Nilpotent
public import CFSG.LieType.AlgebraicGroups.EquivariantAffineEmbedding
public import CFSG.LieType.AlgebraicGroups.UnipotentFinitePoints
public import CFSG.LinearAlgebra.UnipotentPolynomialPowers
public import CFSG.GroupTheory.CoprimeNilpotentHomogeneous
public import TauCeti.Algebra.AlgebraicGroup.Torus.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Torus.Existence
public import CFSG.LieType.AlgebraicGroups.ConnectedCenterAutomorphism
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CategoryTheory WithConv
open scoped TensorProduct

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem isNilpotent_points_of_forall_isUnipotentPoint
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    (hH : ∀ g : WithConv (H →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint g) :
    Group.IsNilpotent (WithConv (H →ₐ[k] k)) := by
  obtain ⟨M, n, b, hb, hclosed⟩ :=
    TauCeti.Comodule.upperUnitriangularCoordinateGroupSchemeHom.exists_isClosedImmersion_of_forall_isUnipotentPoint
      (k := k) (H := H) hH
  let f := TauCeti.Comodule.upperUnitriangularCoordinateBialgHom (H := H) b hb
  have hf : Function.Surjective f :=
    (TauCeti.Comodule.isClosedImmersion_upperUnitriangularCoordinateGroupSchemeHom_iff b hb).mp
      hclosed
  let ρ := TauCeti.AlgHom.mapDomain (A := k) f
  have hinj : Function.Injective ρ := by
    intro g h heq
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := hf x
    have h := congrArg (fun g : WithConv
      (TauCeti.UpperUnitriangular.coordinateHopfAlgebra k (Fin n) →ₐ[k] k) => g.ofConv y) heq
    simpa only [ρ, TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom] using h
  let := TauCeti.UpperUnitriangular.isNilpotent_points k (Fin n) k
  apply Subgroup.isNilpotent_of_ker_le_center ρ
  intro g hg
  have hg1 : g = 1 := hinj ((MonoidHom.mem_ker.mp hg).trans (map_one ρ).symm)
  rw [hg1]
  exact Subgroup.one_mem _

omit [IsAlgClosed k] in
theorem exists_uniform_pow_eq_one_of_unipotent
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (N : Subgroup (WithConv (H →ₐ[k] k)))
    (hN : ∀ g ∈ N, TauCeti.HopfAlgebra.IsUnipotentPoint g)
    {p : ℕ} [CharP k p] (hp : p.Prime) :
    ∃ e : ℕ, ∀ g ∈ N, g ^ (p ^ e) = 1 := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k H).out
  obtain ⟨D, hD, hsD⟩ := TauCeti.Subcoalgebra.exists_finiteDimensional_subcoalgebra_of_setFinite
    (k := k) (C := H) (s : Set H) s.finite_toSet
  let : Module.Finite k D.toSubmodule := hD
  let : Module.Finite k D.toRegularSubcomodule := D.toRegularSubcomodule_finite
  have hgen : Algebra.adjoin k (D : Set H) = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Algebra.adjoin_mono hsD
  let e := Nat.log p (Module.finrank k (k ⊗[k] D.toRegularSubcomodule)) + 1
  have hbound : Module.finrank k (k ⊗[k] D.toRegularSubcomodule) ≤ p ^ e :=
    le_of_lt (Nat.lt_pow_succ_log_self hp.one_lt _)
  refine ⟨e, fun g hg => ?_⟩
  have hnil : IsNilpotent
      (TauCeti.Comodule.endOfPoint D.toRegularSubcomodule g.ofConv - 1) :=
    (TauCeti.HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one g).mp
      (hN g hg) (TauCeti.FGComoduleCat.of (R := k) (C := H) D.toRegularSubcomodule)
  have hpow := ReductiveDescent.endOfPoint_pow_prime_pow_eq_one hp e hbound g hnil
  apply basePointsRepresentation_injective_of_generating_subcoalgebra D hgen
  apply LinearMap.ext
  intro x
  apply ReductiveDescent.mk_one_tmul_injective (K := k)
  rw [ReductiveDescent.mk_one_tmul_basePointsRepresentation,
    ReductiveDescent.mk_one_tmul_basePointsRepresentation,
    ReductiveDescent.endOfPoint_pow, hpow, TauCeti.Comodule.endOfPoint_convOne]
  rfl

omit [IsAlgClosed k] in
theorem isPGroup_of_unipotent
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (N : Subgroup (WithConv (H →ₐ[k] k)))
    (hN : ∀ g ∈ N, TauCeti.HopfAlgebra.IsUnipotentPoint g)
    {p : ℕ} [CharP k p] (hp : p.Prime) : IsPGroup p N := by
  obtain ⟨e, he⟩ := exists_uniform_pow_eq_one_of_unipotent H N hN hp
  exact fun g => ⟨e, Subtype.ext (by simpa only [Subgroup.coe_pow, Subgroup.coe_one] using he g g.property)⟩


section CharZero

variable [CharZero k]

omit [IsAlgClosed k] [CharZero k] in
theorem isNilpotent_toMatrix_basePointsRepresentation_sub_one
    {H M : Type u} [CommRing H] [HopfAlgebra k H]
    [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M] [Module.Finite k M]
    {n : ℕ} (b : Module.Basis (Fin n) k M) (g : WithConv (H →ₐ[k] k))
    (hg : TauCeti.HopfAlgebra.IsUnipotentPoint g) :
    IsNilpotent
      (LinearMap.toMatrixAlgEquiv b
        (TauCeti.Comodule.basePointsRepresentation (H := H) M g) - 1) := by
  have hn : IsNilpotent (TauCeti.Comodule.endOfPoint M g.ofConv - 1) :=
    (TauCeti.HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one g).mp
      hg (TauCeti.FGComoduleCat.of (R := k) (C := H) M)
  have heq : (TensorProduct.lid k M).conjRingEquiv
      (TauCeti.Comodule.endOfPoint M g.ofConv) =
    TauCeti.Comodule.basePointsRepresentation (H := H) M g := by
    apply LinearMap.ext
    intro m
    rw [LinearEquiv.conjRingEquiv_apply_apply,
      TauCeti.Comodule.basePointsRepresentation_apply]
    congr 1
  let e : Module.End k (k ⊗[k] M) ≃+* Module.End k M := (TensorProduct.lid k M).conjRingEquiv
  have heq' : e (TauCeti.Comodule.endOfPoint M g.ofConv) =
      TauCeti.Comodule.basePointsRepresentation (H := H) M g := heq
  have hbase := hn.map e
  have hbase' : IsNilpotent (TauCeti.Comodule.basePointsRepresentation (H := H) M g - 1) := by
    have hs := e.map_sub (TauCeti.Comodule.endOfPoint M g.ofConv) 1
    have h1 : e (1 : Module.End k (k ⊗[k] M)) = 1 := e.map_one
    rw [heq', h1] at hs
    exact hs ▸ hbase
  have hmat := hbase'.map (LinearMap.toMatrixAlgEquiv b)
  simpa only [map_sub, map_one] using hmat

omit [IsAlgClosed k] in
theorem exists_unipotentPowerCurve_of_matrix_image
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) {n : ℕ}
    (f : TauCeti.GeneralLinear.coordinateHopfAlgebra k n →ₐc[k] H)
    (hf : Function.Surjective f) (g : WithConv (H →ₐ[k] k)) {d : ℕ}
    (hU : ((TauCeti.GeneralLinear.pointsMulEquiv n
      (TauCeti.AlgHom.mapDomain f g) : Matrix (Fin n) (Fin n) k) - 1) ^ d = 0) :
    ∃ b : H →ₐ[k] Polynomial k,
      b.comp f.toAlgHom = CFSG.LinearAlgebra.unipotentPowerCoordinate
        (TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain f g)) hU := by
  let U := TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain f g)
  let c := CFSG.LinearAlgebra.unipotentPowerCoordinate U hU
  have hkill : ∀ a : TauCeti.GeneralLinear.coordinateHopfAlgebra k n,
      f a = 0 → c a = 0 := by
    intro a ha
    apply CFSG.LinearAlgebra.polynomial_eq_of_eval_natCast
    intro r
    have hc := CFSG.LinearAlgebra.unipotentPowerCoordinate_eval_natCast U hU r
    have hUpt : TauCeti.GeneralLinear.generalLinearToPoint (R := k) n U =
        TauCeti.AlgHom.mapDomain f g := by
      simpa only [TauCeti.GeneralLinear.pointsMulEquiv_symm_apply, U] using
        (TauCeti.GeneralLinear.pointsMulEquiv (R := k) (A := k) n).symm_apply_apply
          (TauCeti.AlgHom.mapDomain f g)
    rw [hUpt, ← map_pow] at hc
    have heval := congrArg (fun p : WithConv
      (TauCeti.GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] k) => p.ofConv a) hc
    simpa [c, TauCeti.AlgHom.mapDomain_apply, AlgHom.comp_apply, ha] using heval
  let q : (TauCeti.GeneralLinear.coordinateHopfAlgebra k n ⧸
      RingHom.ker f.toAlgHom.toRingHom) →ₐ[k] Polynomial k :=
    Ideal.Quotient.liftₐ _ c (fun a ha => hkill a ha)
  have hfA : Function.Surjective f.toAlgHom := by
    intro x
    obtain ⟨a, ha⟩ := hf x
    exact ⟨a, ha⟩
  let e : (TauCeti.GeneralLinear.coordinateHopfAlgebra k n ⧸
      RingHom.ker f.toAlgHom.toRingHom) ≃ₐ[k] H :=
    Ideal.quotientKerAlgEquivOfSurjective hfA
  let b : H →ₐ[k] Polynomial k := q.comp e.symm.toAlgHom
  refine ⟨b, ?_⟩
  apply AlgHom.ext
  intro a
  change q ((Ideal.quotientKerAlgEquivOfSurjective (f := f.toAlgHom) hfA).symm
    (f.toAlgHom a)) = c a
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
  rfl


omit [IsAlgClosed k] in
theorem exists_pow_eq_of_unipotent_matrix_image
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) {n : ℕ}
    (f : TauCeti.GeneralLinear.coordinateHopfAlgebra k n →ₐc[k] H)
    (hf : Function.Surjective f) (g : WithConv (H →ₐ[k] k)) {d : ℕ}
    (hU : ((TauCeti.GeneralLinear.pointsMulEquiv n
      (TauCeti.AlgHom.mapDomain f g) : Matrix (Fin n) (Fin n) k) - 1) ^ d = 0)
    {m : ℕ} (hm : m ≠ 0) :
    ∃ h : WithConv (H →ₐ[k] k), h ^ m = g := by
  let U := TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain f g)
  let c := CFSG.LinearAlgebra.unipotentPowerCoordinate U hU
  obtain ⟨b, hb⟩ := exists_unipotentPowerCurve_of_matrix_image H f hf g hU
  have hb' : b.comp f.toAlgHom = c := hb
  let h : WithConv (H →ₐ[k] k) := toConv ((Polynomial.aeval ((m : k)⁻¹)).comp b)
  refine ⟨h, ?_⟩
  have hinj : Function.Injective (TauCeti.AlgHom.mapDomain (A := k) f) := by
    intro x y hxy
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    obtain ⟨a, rfl⟩ := hf a
    have he := congrArg (fun p : WithConv
      (TauCeti.GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] k) => p.ofConv a) hxy
    simpa only [TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom] using he
  apply hinj
  rw [map_pow]
  apply (TauCeti.GeneralLinear.pointsMulEquiv n).injective
  rw [map_pow]
  have hh : TauCeti.AlgHom.mapDomain f h =
      toConv ((Polynomial.aeval ((m : k)⁻¹)).comp c) := by
    simp only [h, TauCeti.AlgHom.mapDomain_apply, AlgHom.comp_assoc, hb']
  rw [hh, CFSG.LinearAlgebra.unipotentPowerCoordinate_eval]
  rw [← TauCeti.GeneralLinear.pointsMulEquiv_symm_apply, MulEquiv.apply_symm_apply]
  exact CFSG.LinearAlgebra.map_unipotentPolynomialPowersUnit_inv_natCast_pow U hU hm

omit [IsAlgClosed k] in
theorem exists_pow_eq_of_isUnipotentPoint
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (g : WithConv (H →ₐ[k] k)) (hg : TauCeti.HopfAlgebra.IsUnipotentPoint g)
    {m : ℕ} (hm : m ≠ 0) :
    ∃ h : WithConv (H →ₐ[k] k), h ^ m = g := by
  obtain ⟨D, hD, _, hgen⟩ := exists_finite_invariant_generating_subcoalgebra_three H
    (BialgHom.id k H) (by rfl)
  let : Module.Finite k D.toSubmodule := hD
  let : Module.Finite k D.toRegularSubcomodule := D.toRegularSubcomodule_finite
  let : AddCommGroup D.toRegularSubcomodule := Module.addCommMonoidToAddCommGroup k
  let b := Module.finBasis k D.toRegularSubcomodule
  let f := TauCeti.Comodule.coordinateBialgHom (H := H) b
  have hnil := isNilpotent_toMatrix_basePointsRepresentation_sub_one b g hg
  rw [← pointsMulEquiv_coordinateBialgHom_eq_toMatrix b g] at hnil
  obtain ⟨d, hd⟩ := hnil
  exact exists_pow_eq_of_unipotent_matrix_image H f
    (coordinateBialgHom_surjective_of_generating_subcoalgebra D hgen b) g hd hm

omit [IsAlgClosed k] in
theorem pow_injective_of_forall_isUnipotentPoint
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hH : ∀ g : WithConv (H →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint g)
    {m : ℕ} (hm : m ≠ 0) :
    Function.Injective (fun g : WithConv (H →ₐ[k] k) => g ^ m) := by
  obtain ⟨D, hD, _, hgen⟩ := exists_finite_invariant_generating_subcoalgebra_three H
    (BialgHom.id k H) (by rfl)
  let : Module.Finite k D.toSubmodule := hD
  let : Module.Finite k D.toRegularSubcomodule := D.toRegularSubcomodule_finite
  let : AddCommGroup D.toRegularSubcomodule := Module.addCommMonoidToAddCommGroup k
  let b := Module.finBasis k D.toRegularSubcomodule
  let f := TauCeti.Comodule.coordinateBialgHom (H := H) b
  let ρ : WithConv (H →ₐ[k] k) →* Matrix.GeneralLinearGroup (Fin
      (Module.finrank k D.toRegularSubcomodule)) k :=
    (TauCeti.GeneralLinear.pointsMulEquiv _).toMonoidHom.comp (TauCeti.AlgHom.mapDomain f)
  intro g h hpow
  have hg := isNilpotent_toMatrix_basePointsRepresentation_sub_one b g (hH g)
  have hh := isNilpotent_toMatrix_basePointsRepresentation_sub_one b h (hH h)
  rw [← pointsMulEquiv_coordinateBialgHom_eq_toMatrix b g] at hg
  rw [← pointsMulEquiv_coordinateBialgHom_eq_toMatrix b h] at hh
  have hmatrix : ρ g = ρ h := CFSG.LinearAlgebra.eq_of_pow_eq_of_isUnipotent
    (ρ g) (ρ h) hg hh hm (by simpa only [map_pow] using congrArg ρ hpow)
  apply basePointsRepresentation_injective_of_generating_subcoalgebra D hgen
  apply (LinearMap.toMatrixAlgEquiv b).injective
  rw [← pointsMulEquiv_coordinateBialgHom_eq_toMatrix b g,
    ← pointsMulEquiv_coordinateBialgHom_eq_toMatrix b h]
  exact congrArg Units.val hmatrix


end CharZero


omit [IsAlgClosed k] in
theorem pow_bijective_of_unipotent
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hH : ∀ g : WithConv (H →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint g)
    {m : ℕ} (hm : (m : k) ≠ 0) :
    Function.Bijective (fun g : WithConv (H →ₐ[k] k) => g ^ m) := by
  by_cases hchar : CharZero k
  · let := hchar
    have hm0 : m ≠ 0 := by rintro rfl; exact hm Nat.cast_zero
    exact ⟨pow_injective_of_forall_isUnipotentPoint H hH hm0,
      fun g => exists_pow_eq_of_isUnipotentPoint H g (hH g) hm0⟩
  · have hp0 : ringChar k ≠ 0 := fun h =>
      hchar ((CharP.ringChar_zero_iff_CharZero k).mp h)
    have hp : (ringChar k).Prime :=
      (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hp0
    let : Fact (ringChar k).Prime := ⟨hp⟩
    have hcop : ¬ ringChar k ∣ m := fun h => hm ((CharP.cast_eq_zero_iff k (ringChar k) m).mpr h)
    let N := (⊤ : Subgroup (WithConv (H →ₐ[k] k)))
    have hN : Function.Bijective (fun g : N => g ^ m) :=
      (IsPGroup.powEquiv' (isPGroup_of_unipotent H N (fun g _ => hH g) hp) hcop).bijective
    constructor
    · intro g h heq
      have h := hN.1 (show (⟨g, Subgroup.mem_top g⟩ : N) ^ m =
        ⟨h, Subgroup.mem_top h⟩ ^ m from Subtype.ext heq)
      exact congrArg Subtype.val h
    · intro g
      obtain ⟨h, hh⟩ := hN.2 ⟨g, Subgroup.mem_top g⟩
      exact ⟨h, congrArg Subtype.val hh⟩


abbrev MaximalTorusIdeals (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :=
  {I : TauCeti.HopfIdeal k B // TauCeti.HopfIdeal.IsMaximalTorus k B.obj I}

noncomputable instance maximalTorusIdealsMulAction
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    MulAction (WithConv (B →ₐ[k] k)) (MaximalTorusIdeals B) where
  smul g I := ⟨I.val.conjugate g, I.property.conjugate g⟩
  one_smul I := Subtype.ext (TauCeti.HopfIdeal.conjugate_one I.val)
  mul_smul g h I := Subtype.ext (TauCeti.HopfIdeal.conjugate_mul I.val g h)

instance maximalTorusIdealsNonempty (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    Nonempty (MaximalTorusIdeals B) := by
  obtain ⟨I, hI⟩ := TauCeti.HopfIdeal.exists_isMaximalTorus B
  exact ⟨⟨I, hI⟩⟩


abbrev unipotentRadicalPointsHom (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B →ₐ[k] k) →*
      WithConv (B →ₐ[k] k) :=
  TauCeti.AlgHom.mapDomain
    (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalCoordinateMap B))


noncomputable instance unipotentRadicalMaximalTorusAction
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    MulAction (WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B →ₐ[k] k))
      (MaximalTorusIdeals B) :=
  MulAction.compHom (MaximalTorusIdeals B) (unipotentRadicalPointsHom B)


end CFSG.LieType.AlgebraicGroups
