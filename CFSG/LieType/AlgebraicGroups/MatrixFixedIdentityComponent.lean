module

public import CFSG.LieType.AlgebraicGroups.MatrixFixedComponentsThree

public noncomputable section

open WithConv CategoryTheory
namespace CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

section ConvolutionScoped

open scoped CFSG.ConvolutionPoints

abbrev matrixCentralizerIdeal (M : Subgroup (ModGL τ k)) (a : ModGL τ k) :
    Ideal (GLCoord k (Label τ)) :=
  subgroupIdeal ((M ⊓ Subgroup.centralizer {a}).map (modGLPoint τ k).toMonoidHom)

def matrixFixedBialgHom (M : Subgroup (ModGL τ k)) (a : ModGL τ k)
    (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M) :
    GLCoord k (Label τ) →ₐc[k]
      fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha) :=
  (Bialgebra.Quotient.mkBialgHom (fixedHopfIdeal (MatrixComponents.coordinateHopf M)
    (matrixInnerCoordinate M a ha)).toIdeal).comp
    (Bialgebra.Quotient.mkBialgHom (subgroupIdeal (M.map (modGLPoint τ k).toMonoidHom)))

theorem matrixFixedBialgHom_eq_zero_of_mem (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    [Algebra.Smooth k (MatrixComponents.coordinateHopf M)]
    (h3 : (3 : k) ≠ 0) (ha3 : a ^ 3 = 1) :
    ∀ b ∈ matrixCentralizerIdeal M a, matrixFixedBialgHom M a ha b = 0 := by
  let F := fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha)
  let N := M ⊓ Subgroup.centralizer {a}
  let e := modGLPoint τ k
  let : Algebra.Smooth k F := smooth_fixedCoordinate_three (MatrixComponents.coordinateHopf M)
    h3 (matrixInnerCoordinate M a ha) (matrixInnerCoordinate_cube M a ha ha3)
  let : IsReduced F := TauCeti.isReduced_of_smooth k F
  have hf : ∀ z : F →ₐ[k] k, z.comp (matrixFixedBialgHom M a ha).toAlgHom ∈
      transportPoints e (N : Set (ModGL τ k)) := by
    intro z
    refine ⟨matrixFixedPointsHom M hM a ha (toConv z),
      (matrixFixedPointsHom M hM a ha (toConv z)).property, ?_⟩
    change (e (matrixFixedPointsHom M hM a ha (toConv z) : ModGL τ k)).ofConv = _
    dsimp only [e]
    rw [matrixFixedPointsHom_apply, MatrixComponents.coordinatePointsMulEquiv_coe,
      MulEquiv.apply_symm_apply, ofConv_toConv]
    rfl
  intro b hb
  exact map_eq_zero_of_comp_mem (transportPoints e (N : Set (ModGL τ k)))
    (matrixFixedBialgHom M a ha).toAlgHom hf
    (by simpa only [matrixCentralizerIdeal, subgroupIdeal, subgroupPoints_map] using hb)

def matrixFixedCoordinatePointMap (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    [Algebra.Smooth k (MatrixComponents.coordinateHopf M)]
    (h3 : (3 : k) ≠ 0) (ha3 : a ^ 3 = 1) :
    MatrixComponents.coordinateHopf (M ⊓ Subgroup.centralizer {a}) →ₐc[k]
      fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha) :=
  bialgHomQuotientLift (matrixCentralizerIdeal M a) (matrixFixedBialgHom M a ha)
    (matrixFixedBialgHom_eq_zero_of_mem M hM a ha h3 ha3)

theorem matrixFixedCoordinatePointMap_on_points
    (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    [Algebra.Smooth k (MatrixComponents.coordinateHopf M)]
    (h3 : (3 : k) ≠ 0) (ha3 : a ^ 3 = 1)
    (x : TauCeti.HopfAlgebra.points (R := k)
      (H := fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha))
      (CommAlgCat.of k k)) :
    MatrixComponents.coordinatePointsMulEquiv (M ⊓ Subgroup.centralizer {a})
        (isPointClosed_inf hM (isPointClosed_centralizer {a}))
        (TauCeti.AlgHom.mapDomain (matrixFixedCoordinatePointMap M hM a ha h3 ha3) x) =
      matrixFixedPointsHom M hM a ha x := by
  let F := fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha)
  let N := M ⊓ Subgroup.centralizer {a}
  let e := modGLPoint τ k
  let I := matrixCentralizerIdeal M a
  let fB := matrixFixedBialgHom M a ha
  let hkill := matrixFixedBialgHom_eq_zero_of_mem M hM a ha h3 ha3
  change MatrixComponents.coordinatePointsMulEquiv N
      (isPointClosed_inf hM (isPointClosed_centralizer {a}))
      (TauCeti.AlgHom.mapDomain (bialgHomQuotientLift I fB hkill) x) = _
  apply Subtype.ext
  rw [MatrixComponents.coordinatePointsMulEquiv_coe, matrixFixedPointsHom_apply,
    MatrixComponents.coordinatePointsMulEquiv_coe]
  apply congrArg e.symm
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro b
  change x.ofConv (bialgHomQuotientLift I fB hkill (Ideal.Quotient.mk I b)) = x.ofConv (fB b)
  rw [bialgHomQuotientLift_mk]

theorem matrixFixedCoordinatePointMap_bijective
    (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    [Algebra.Smooth k (MatrixComponents.coordinateHopf M)]
    (h3 : (3 : k) ≠ 0) (ha3 : a ^ 3 = 1) :
    Function.Bijective (matrixFixedCoordinatePointMap M hM a ha h3 ha3) := by
  let F := fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha)
  let N := M ⊓ Subgroup.centralizer {a}
  let hN := isPointClosed_inf hM (isPointClosed_centralizer {a})
  let e := modGLPoint τ k
  let I := matrixCentralizerIdeal M a
  let fB := matrixFixedBialgHom M a ha
  let hkill := matrixFixedBialgHom_eq_zero_of_mem M hM a ha h3 ha3
  let qF : MatrixComponents.coordinateHopf M →ₐc[k] F :=
    Bialgebra.Quotient.mkBialgHom
      (fixedHopfIdeal (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha)).toIdeal
  let πb : GLCoord k (Label τ) →ₐc[k] MatrixComponents.coordinateHopf M :=
    Bialgebra.Quotient.mkBialgHom (subgroupIdeal (M.map e.toMonoidHom))
  have hπb : Function.Surjective πb := by
    intro x
    obtain ⟨b, hb⟩ := Ideal.Quotient.mkₐ_surjective k
      (subgroupIdeal (M.map e.toMonoidHom)) x
    exact ⟨b, by simpa only [πb, Bialgebra.Quotient.mkBialgHom_apply,
      Ideal.Quotient.mkₐ_eq_mk] using hb⟩
  have hqF : Function.Surjective qF := by
    intro y
    obtain ⟨c, hc⟩ := Ideal.Quotient.mkₐ_surjective k
      (fixedHopfIdeal (MatrixComponents.coordinateHopf M)
        (matrixInnerCoordinate M a ha)).toIdeal y
    exact ⟨c, by rw [Bialgebra.Quotient.mkBialgHom_apply]; exact hc⟩
  have hfB : Function.Surjective fB := by
    change Function.Surjective (qF.comp πb)
    exact hqF.comp hπb
  refine ⟨?_, ?_⟩
  ·
    have hker : ∀ b, bialgHomQuotientLift I fB hkill b = 0 → b = 0 := by
      intro b hb
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hc0 : fB c = 0 := by
        rwa [bialgHomQuotientLift_mk] at hb
      rw [Ideal.Quotient.eq_zero_iff_mem]
      change c ∈ pointsIdeal (subgroupPoints (N.map e.toMonoidHom))
      rw [mem_pointsIdeal]
      intro y hy
      have hyN : (e.symm (toConv y) : ModGL τ k) ∈ N := (Subgroup.mem_map_equiv).mp hy
      obtain ⟨x, hx⟩ := (matrixFixedPointsHom_bijective M hM a ha).2
        (⟨e.symm (toConv y), hyN⟩ : N)
      have hθ := matrixFixedCoordinatePointMap_on_points M hM a ha h3 ha3 x
      have hx' : matrixFixedPointsHom M hM a ha x = ⟨e.symm (toConv y), hyN⟩ := hx
      let z : TauCeti.HopfAlgebra.points (H := MatrixComponents.coordinateHopf N)
          (CommAlgCat.of k k) :=
        toConv (Ideal.Quotient.liftₐ I y (fun b hb => by
          have h := (mem_subgroupIdeal (H := N.map e.toMonoidHom)).1 hb (toConv y) hy
          simpa only [ofConv_toConv] using h))
      have hz : MatrixComponents.coordinatePointsMulEquiv N hN z = ⟨e.symm (toConv y), hyN⟩ := by
        apply Subtype.ext
        rw [MatrixComponents.coordinatePointsMulEquiv_coe]
        congr 1
      have hzeq : z = TauCeti.AlgHom.mapDomain
          (matrixFixedCoordinatePointMap M hM a ha h3 ha3) x := by
        apply (MatrixComponents.coordinatePointsMulEquiv N hN).injective
        rw [hz, hθ, hx']
      have h1 : z (Ideal.Quotient.mk I c) = y c := rfl
      have h2 : (TauCeti.AlgHom.mapDomain
          (matrixFixedCoordinatePointMap M hM a ha h3 ha3) x)
          (Ideal.Quotient.mk I c) = 0 := by
        rw [TauCeti.AlgHom.mapDomain_apply_apply]
        change x.ofConv (bialgHomQuotientLift I fB hkill (Ideal.Quotient.mk I c)) = 0
        rw [bialgHomQuotientLift_mk, hc0]
        exact map_zero x.ofConv
      rw [← h1, hzeq, h2]
    refine fun b b' hbb => ?_
    have hbb' : bialgHomQuotientLift I fB hkill b =
        bialgHomQuotientLift I fB hkill b' := hbb
    have h : b - b' = 0 := hker (b - b') (by rw [map_sub, hbb', sub_self])
    exact sub_eq_zero.mp h
  ·
    intro y
    obtain ⟨b, rfl⟩ := hfB y
    exact ⟨Ideal.Quotient.mk I b, bialgHomQuotientLift_mk I fB hkill b⟩


theorem smooth_coordinateHopf_centralizer
    (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    [Algebra.Smooth k (MatrixComponents.coordinateHopf M)]
    (h3 : (3 : k) ≠ 0) (ha3 : a ^ 3 = 1) :
    Algebra.Smooth k (MatrixComponents.coordinateHopf (M ⊓ Subgroup.centralizer {a})) := by
  let : Algebra.Smooth k
      (fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha)) :=
    smooth_fixedCoordinate_three (MatrixComponents.coordinateHopf M) h3
      (matrixInnerCoordinate M a ha) (matrixInnerCoordinate_cube M a ha ha3)
  exact Algebra.Smooth.of_equiv
    (BialgEquiv.ofBijective (matrixFixedCoordinatePointMap M hM a ha h3 ha3)
      (matrixFixedCoordinatePointMap_bijective M hM a ha h3 ha3)).symm.toAlgEquiv


end ConvolutionScoped

end CFSG.LieType.AlgebraicGroups
