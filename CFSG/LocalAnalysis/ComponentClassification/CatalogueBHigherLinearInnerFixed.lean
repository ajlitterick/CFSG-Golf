module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport

public section

namespace CFSG.ComponentClassification.CatalogueBHigherLinearInner

noncomputable section

open CatalogueBHigherLinearAction

universe u

instance pglFinite (n : ℕ) (K : Type u) [Field K] [Finite K] :
    Finite (Matrix.ProjGenLinGroup (Fin n) K) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

abbrev pglCentralizer (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) :=
  Subgroup.centralizer ({a} : Set (Matrix.ProjGenLinGroup (Fin n) K))

abbrev localPSLRange (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) : Subgroup (pglCentralizer n K a) :=
  (pslRange n K).subgroupOf (pglCentralizer n K a)

instance localPSLRangeNormal (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) : (localPSLRange n K a).Normal := by
  change ((pslRange n K).comap (pglCentralizer n K a).subtype).Normal
  infer_instance

theorem pslRangeEquiv_pglAction (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) :
    MulAut.congr (pslRangeEquiv n K) (pglAction n K a) =
      MulAut.conjNormal (H := pslRange n K) a := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
    (pglAction n K a ((pslRangeEquiv n K).symm x)) = a * x.val * a⁻¹
  rw [toPGL_pglAction, pslRangeEquiv_symm_toPGL]

@[expose] def fixedPSLCentralizerEquiv (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) :
    FixedCommutingProduct.fixedSubgroup (pglAction n K a) ≃* localPSLRange n K a :=
  (CatalogueRelativeB.fixedSubgroupEquivalence (pslRangeEquiv n K) (pglAction n K a)).trans
    ((MulEquiv.subgroupCongr (congrArg FixedCommutingProduct.fixedSubgroup
      (pslRangeEquiv_pglAction n K a))).trans
      (FixedNormalCentralizer.equivalence (pslRange n K) a).symm)


@[expose] def innerFixedCentralizerEquiv (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    FixedCommutingProduct.fixedSubgroup (innerDiagonalAction n K A) ≃*
      localPSLRange n K (Matrix.ProjGenLinGroup.mk A) :=
  fixedPSLCentralizerEquiv n K (Matrix.ProjGenLinGroup.mk A)


theorem pComponent_fixed_image (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) (p : ℕ)
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup (pglAction n K a)))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p (L.map (fixedPSLCentralizerEquiv n K a).toMonoidHom) :=
  CatalogueBAlternating.pComponent_map_equiv p (fixedPSLCentralizerEquiv n K a) L hL

theorem pComponent_fixed_extend (n : ℕ) (K : Type u) [Field K] [Finite K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup (pglAction n K a)))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p
      ((L.map (fixedPSLCentralizerEquiv n K a).toMonoidHom).map
        (localPSLRange n K a).subtype) :=
  CatalogueBAlternating.pComponent_of_normal_subgroup p (localPSLRange n K a)
    (L.map (fixedPSLCentralizerEquiv n K a).toMonoidHom)
    (pComponent_fixed_image n K a p L hL)


end

end CFSG.ComponentClassification.CatalogueBHigherLinearInner
