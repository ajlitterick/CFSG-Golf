module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import CFSG.LocalAnalysis.ZStar.TwoAdicWedderburn
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG

namespace ZStar.ComponentIntegralLattice

noncomputable section

universe uR uK uG uV uI

variable {R : Type uR} {K : Type uK} {G : Type uG}
  {V : Type uV} {ι : Type uI}
  [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Group G] [Fintype G]
  [AddCommGroup V] [Module K V] [Module R V]
  [IsScalarTower R K V] [Module.IsTorsionFree R V]
  [Fintype ι]

@[expose] def orbitSpan (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Submodule R V :=
  Submodule.span R
    (Set.range fun p : G × ι => ρ p.1 (b p.2))

instance orbitSpan_moduleFinite
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Module.Finite R (orbitSpan (R := R) ρ b) :=
  Module.Finite.span_of_finite R
    (Set.finite_range fun p : G × ι => ρ p.1 (b p.2))

instance orbitSpan_isTorsionFree
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Module.IsTorsionFree R (orbitSpan (R := R) ρ b) :=
  Submodule.instIsTorsionFree (orbitSpan (R := R) ρ b)

instance orbitSpan_moduleFlat
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Module.Flat R (orbitSpan (R := R) ρ b) :=
  (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)

instance orbitSpan_moduleFree
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Module.Free R (orbitSpan (R := R) ρ b) :=
  Module.free_of_flat_of_isLocalRing

omit [IsDomain R] [IsBezout R] [IsLocalRing R] [IsFractionRing R K] [Fintype G]
  [Module.IsTorsionFree R V] [Fintype ι] in
theorem orbitSpan_stable
    (ρ : Representation K G V) (b : Module.Basis ι K V) (g : G) :
    Set.MapsTo (ρ g) (orbitSpan (R := R) ρ b) (orbitSpan (R := R) ρ b) := by
  change Set.MapsTo (⇑((ρ g).restrictScalars R))
    (orbitSpan (R := R) ρ b) (orbitSpan (R := R) ρ b)
  unfold orbitSpan
  apply Submodule.mapsTo_span
  rintro _ ⟨⟨h, i⟩, rfl⟩
  refine ⟨⟨g * h, i⟩, ?_⟩
  change ρ (g * h) (b i) = ρ g (ρ h (b i))
  rw [map_mul]
  rfl

omit [IsDomain R] [IsBezout R] [IsLocalRing R] [IsFractionRing R K] [Fintype G]
  [Module.IsTorsionFree R V] [Fintype ι] in

@[expose] def orbitSpanEnd
    (ρ : Representation K G V) (b : Module.Basis ι K V) (g : G) :
    Module.End R (orbitSpan (R := R) ρ b) :=
  ((ρ g).restrictScalars R).restrict fun _x hx =>
    orbitSpan_stable (R := R) ρ b g hx

omit [IsDomain R] [IsBezout R] [IsLocalRing R] [IsFractionRing R K] [Fintype G]
  [Module.IsTorsionFree R V] [Fintype ι] in
@[simp]
theorem orbitSpanEnd_apply
    (ρ : Representation K G V) (b : Module.Basis ι K V) (g : G)
    (x : orbitSpan (R := R) ρ b) :
    ((orbitSpanEnd (R := R) ρ b g x : orbitSpan (R := R) ρ b) : V) =
      ρ g x :=
  rfl

omit [IsDomain R] [IsBezout R] [IsLocalRing R] [IsFractionRing R K] [Fintype G]
  [Module.IsTorsionFree R V] [Fintype ι] in
theorem orbitSpanEnd_one
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    orbitSpanEnd (R := R) ρ b 1 = 1 := by
  ext x
  change ρ 1 x = x
  simp

omit [IsDomain R] [IsBezout R] [IsLocalRing R] [IsFractionRing R K] [Fintype G]
  [Module.IsTorsionFree R V] [Fintype ι] in
theorem orbitSpanEnd_mul
    (ρ : Representation K G V) (b : Module.Basis ι K V) (g h : G) :
    orbitSpanEnd (R := R) ρ b (g * h) =
      orbitSpanEnd (R := R) ρ b g * orbitSpanEnd (R := R) ρ b h := by
  ext x
  change ρ (g * h) x = ρ g (ρ h x)
  rw [map_mul]
  rfl

omit [IsDomain R] [IsBezout R] [IsLocalRing R] [IsFractionRing R K]
  [Fintype G] [Module.IsTorsionFree R V] [Fintype ι] in
@[expose] def orbitSpanRepresentation
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Representation R G (orbitSpan (R := R) ρ b) where
  toFun := orbitSpanEnd (R := R) ρ b
  map_one' := orbitSpanEnd_one (R := R) ρ b
  map_mul' := orbitSpanEnd_mul (R := R) ρ b

omit [IsDomain R] [IsBezout R] [IsLocalRing R] [IsFractionRing R K]
  [Fintype G] [Module.IsTorsionFree R V] [Fintype ι] in
@[simp]
theorem orbitSpanRepresentation_apply
    (ρ : Representation K G V) (b : Module.Basis ι K V) (g : G)
    (x : orbitSpan (R := R) ρ b) :
    (((orbitSpanRepresentation (R := R) ρ b) g x :
        orbitSpan (R := R) ρ b) : V) = ρ g x :=
  rfl

omit [IsDomain R] [IsBezout R] [IsLocalRing R] [Algebra R K]
  [IsFractionRing R K] [Fintype G]
  [IsScalarTower R K V] [Module.IsTorsionFree R V] [Fintype ι] in
private theorem span_orbitSpan_eq_top
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Submodule.span K (orbitSpan (R := R) ρ b : Set V) = ⊤ := by
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨1, i⟩, ?_⟩
  simp

@[expose] def orbitSpanBasis
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Module.Basis (Fin (Module.finrank R (orbitSpan (R := R) ρ b))) R
      (orbitSpan (R := R) ρ b) :=
  Module.finBasis R (orbitSpan (R := R) ρ b)

@[expose] def orbitSpanBasisCoe
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Fin (Module.finrank R (orbitSpan (R := R) ρ b)) → V :=
  fun j => orbitSpanBasis (R := R) ρ b j

omit [Algebra R K] [IsFractionRing R K] [IsScalarTower R K V] in
@[simp]
theorem orbitSpanBasisCoe_apply
    (ρ : Representation K G V) (b : Module.Basis ι K V)
    (j : Fin (Module.finrank R (orbitSpan (R := R) ρ b))) :
    orbitSpanBasisCoe (R := R) ρ b j =
      ((orbitSpanBasis (R := R) ρ b j :
        orbitSpan (R := R) ρ b) : V) :=
  rfl

theorem orbitSpanBasisCoe_linearIndependent
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    LinearIndependent K (orbitSpanBasisCoe (R := R) ρ b) := by
  apply (LinearIndependent.iff_fractionRing R K).mp
  have h := (orbitSpanBasis (R := R) ρ b).linearIndependent.map_injOn
    (orbitSpan (R := R) ρ b).subtype
    (Submodule.injective_subtype (orbitSpan (R := R) ρ b)).injOn
  change LinearIndependent R
    (fun j => ((orbitSpanBasis (R := R) ρ b j :
      orbitSpan (R := R) ρ b) : V))
  convert h using 1
  funext j
  rfl

omit [Algebra R K] [IsFractionRing R K] [IsScalarTower R K V] in
private theorem span_orbitSpanBasisCoe_eq_orbitSpan
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Submodule.span R (Set.range (orbitSpanBasisCoe (R := R) ρ b)) =
      orbitSpan (R := R) ρ b := by
  rw [show Set.range (orbitSpanBasisCoe (R := R) ρ b) =
      (orbitSpan (R := R) ρ b).subtype ''
        Set.range (orbitSpanBasis (R := R) ρ b) by
    rw [← Set.range_comp']
    rfl]
  rw [← LinearMap.map_span, (orbitSpanBasis (R := R) ρ b).span_eq,
    Submodule.map_subtype_top]

omit [IsFractionRing R K] in
private theorem span_orbitSpanBasisCoe_eq_top
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Submodule.span K (Set.range (orbitSpanBasisCoe (R := R) ρ b)) = ⊤ := by
  calc
    Submodule.span K (Set.range (orbitSpanBasisCoe (R := R) ρ b)) =
        Submodule.span K
          (Submodule.span R
            (Set.range (orbitSpanBasisCoe (R := R) ρ b)) : Set V) :=
      (Submodule.span_span_of_tower R K
        (Set.range (orbitSpanBasisCoe (R := R) ρ b))).symm
    _ = Submodule.span K (orbitSpan (R := R) ρ b : Set V) := by
      rw [span_orbitSpanBasisCoe_eq_orbitSpan]
    _ = ⊤ := span_orbitSpan_eq_top (R := R) ρ b

@[expose] def orbitSpanFieldBasis
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Module.Basis (Fin (Module.finrank R (orbitSpan (R := R) ρ b))) K V :=
  Module.Basis.mk (orbitSpanBasisCoe_linearIndependent (R := R) ρ b) (by
    rw [span_orbitSpanBasisCoe_eq_top])

@[simp]
theorem orbitSpanFieldBasis_apply
    (ρ : Representation K G V) (b : Module.Basis ι K V)
    (j : Fin (Module.finrank R (orbitSpan (R := R) ρ b))) :
    orbitSpanFieldBasis (R := R) ρ b j =
      orbitSpanBasisCoe (R := R) ρ b j := by
  exact Module.Basis.mk_apply _ _ _

private theorem orbitSpanSubtype_isBaseChange
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    IsBaseChange K (orbitSpan (R := R) ρ b).subtype := by
  let βR := orbitSpanBasis (R := R) ρ b
  let βK := orbitSpanFieldBasis (R := R) ρ b
  have hcomb :
      IsBaseChange K (Finsupp.linearCombination R (⇑βK)) :=
    IsBaseChange.of_basis R βK
  have hcomp := IsBaseChange.comp_equiv βR.repr
    (Finsupp.linearCombination R (⇑βK)) hcomb
  have heq :
      (Finsupp.linearCombination R (⇑βK)).comp βR.repr.toLinearMap =
        (orbitSpan (R := R) ρ b).subtype := by
    apply βR.ext
    intro j
    simp [βR, βK, orbitSpanFieldBasis_apply, orbitSpanBasisCoe_apply]
  rw [← heq]
  exact hcomp


private theorem orbitSpanEnd_baseChange
    (ρ : Representation K G V) (b : Module.Basis ι K V) (g : G) :
    (orbitSpanSubtype_isBaseChange (R := R) ρ b).endHom
        (orbitSpanEnd (R := R) ρ b g) = ρ g := by
  apply (orbitSpanSubtype_isBaseChange (R := R) ρ b).algHom_ext
  intro x
  rw [IsBaseChange.endHom_comp_apply]
  rfl

private theorem finrank_orbitSpan_eq
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Module.finrank R (orbitSpan (R := R) ρ b) = Module.finrank K V := by
  have h := Module.finrank_eq_card_basis (orbitSpanFieldBasis (R := R) ρ b)
  simpa using h.symm


open ZStar.PadicBlockField
open ZStar.TwoAdicWedderburn

abbrev O2 := PadicComplexInt 2

attribute [local instance 2000] CommRing.toCommSemiring

theorem algebraMap_O2_TwoAdicComplex_injective :
    Function.Injective (algebraMap O2 TwoAdicComplex) :=
  IsFractionRing.injective O2 TwoAdicComplex

section Component

universe u

variable {G₀ : Type u} [Group G₀] [Fintype G₀]

@[expose] def componentStandardBasis (D : Decomposition G₀) (i : Fin D.blockCount) :
    Module.Basis (Fin (D.blockSize i)) TwoAdicComplex
      (Fin (D.blockSize i) → TwoAdicComplex) :=
  Pi.basisFun TwoAdicComplex (Fin (D.blockSize i))

abbrev componentOrbitLattice (D : Decomposition G₀) (i : Fin D.blockCount) :
    Submodule O2 (Fin (D.blockSize i) → TwoAdicComplex) :=
  orbitSpan (R := O2) (componentRepresentation D i)
    (componentStandardBasis D i)

theorem componentOrbitLattice_finrank
    (D : Decomposition G₀) (i : Fin D.blockCount) :
    Module.finrank O2 (componentOrbitLattice D i) = D.blockSize i := by
  calc
    Module.finrank O2 (componentOrbitLattice D i) =
        Module.finrank TwoAdicComplex
          (Fin (D.blockSize i) → TwoAdicComplex) := by
      exact finrank_orbitSpan_eq (R := O2)
        (componentRepresentation D i) (componentStandardBasis D i)
    _ = D.blockSize i := Module.finrank_fin_fun TwoAdicComplex

@[expose] def componentIndexEquiv (D : Decomposition G₀) (i : Fin D.blockCount) :
    Fin (Module.finrank O2 (componentOrbitLattice D i)) ≃
      Fin (D.blockSize i) :=
  finCongr (componentOrbitLattice_finrank D i)

@[expose] def componentIntegralBasis (D : Decomposition G₀)
    (i : Fin D.blockCount) :
    Module.Basis (Fin (D.blockSize i)) O2 (componentOrbitLattice D i) :=
  (orbitSpanBasis (R := O2) (componentRepresentation D i)
    (componentStandardBasis D i)).reindex (componentIndexEquiv D i)

@[expose] def componentIntegralRepresentation (D : Decomposition G₀)
    (i : Fin D.blockCount) :
    Representation O2 G₀ (componentOrbitLattice D i) :=
  orbitSpanRepresentation (R := O2) (componentRepresentation D i)
    (componentStandardBasis D i)

@[simp]
theorem componentIntegralRepresentation_apply
    (D : Decomposition G₀) (i : Fin D.blockCount) (g : G₀)
    (x : componentOrbitLattice D i) :
    (((componentIntegralRepresentation D i) g x :
        componentOrbitLattice D i) :
      Fin (D.blockSize i) → TwoAdicComplex) =
      componentRepresentation D i g x :=
  rfl

@[expose] def componentFieldBasis (D : Decomposition G₀) (i : Fin D.blockCount) :
    Module.Basis (Fin (D.blockSize i)) TwoAdicComplex
      (Fin (D.blockSize i) → TwoAdicComplex) :=
  (orbitSpanFieldBasis (R := O2) (componentRepresentation D i)
    (componentStandardBasis D i)).reindex (componentIndexEquiv D i)

private theorem componentBaseChangeBasis_eq
    (D : Decomposition G₀) (i : Fin D.blockCount) :
    (orbitSpanSubtype_isBaseChange (R := O2) (componentRepresentation D i)
        (componentStandardBasis D i)).basis (componentIntegralBasis D i) =
      componentFieldBasis D i := by
  ext j
  rw [IsBaseChange.basis_apply]
  simp [componentIntegralBasis, componentFieldBasis,
    Module.Basis.reindex_apply, orbitSpanFieldBasis_apply]

@[expose] def componentIntegralMatrix (D : Decomposition G₀)
    (i : Fin D.blockCount) (g : G₀) :
    Matrix (Fin (D.blockSize i)) (Fin (D.blockSize i)) O2 :=
  LinearMap.toMatrix (componentIntegralBasis D i) (componentIntegralBasis D i)
    (orbitSpanEnd (R := O2) (componentRepresentation D i)
      (componentStandardBasis D i) g)

theorem componentIntegralRepresentation_toMatrix
    (D : Decomposition G₀) (i : Fin D.blockCount) (g : G₀) :
    LinearMap.toMatrix (componentIntegralBasis D i) (componentIntegralBasis D i)
        ((componentIntegralRepresentation D i) g) =
      componentIntegralMatrix D i g :=
  rfl

theorem componentIntegralMatrix_map_algebraMap
    (D : Decomposition G₀) (i : Fin D.blockCount) (g : G₀) :
    (componentIntegralMatrix D i g).map (algebraMap O2 TwoAdicComplex) =
      LinearMap.toMatrix (componentFieldBasis D i) (componentFieldBasis D i)
        (componentRepresentation D i g) := by
  have h := IsBaseChange.endHom_toMatrix TwoAdicComplex
    (componentOrbitLattice D i)
    (orbitSpanSubtype_isBaseChange (R := O2) (componentRepresentation D i)
      (componentStandardBasis D i))
    (componentIntegralBasis D i)
    (orbitSpanEnd (R := O2) (componentRepresentation D i)
      (componentStandardBasis D i) g)
  rw [componentBaseChangeBasis_eq, orbitSpanEnd_baseChange] at h
  exact h.symm

theorem componentIntegralMatrix_one
    (D : Decomposition G₀) (i : Fin D.blockCount) :
    componentIntegralMatrix D i 1 = 1 := by
  rw [componentIntegralMatrix, orbitSpanEnd_one, LinearMap.toMatrix_one]

theorem componentIntegralMatrix_mul
    (D : Decomposition G₀) (i : Fin D.blockCount) (g h : G₀) :
    componentIntegralMatrix D i (g * h) =
      componentIntegralMatrix D i g * componentIntegralMatrix D i h := by
  rw [componentIntegralMatrix, orbitSpanEnd_mul, LinearMap.toMatrix_mul]
  rfl

theorem componentIntegralMatrix_sq_of_sq_one
    (D : Decomposition G₀) (i : Fin D.blockCount) (w : G₀)
    (hw : w * w = 1) :
    componentIntegralMatrix D i w * componentIntegralMatrix D i w = 1 := by
  rw [← componentIntegralMatrix_mul, hw, componentIntegralMatrix_one]


end Component

end

end ZStar.ComponentIntegralLattice

end CFSG
