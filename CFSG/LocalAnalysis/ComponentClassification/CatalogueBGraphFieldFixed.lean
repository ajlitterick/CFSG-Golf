module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldFixed

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHigherLinearAction

universe u

abbrev fixedPGL (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Subgroup (ProjGenLinGroup (Fin n) K) :=
  TauCeti.fixedSubgroup (pglGraphFieldAut n K sigma).toMonoidHom

abbrev fixedPSL (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Subgroup (ProjectiveSpecialLinearGroup (Fin n) K) :=
  TauCeti.fixedSubgroup (pslGraphFieldAut n K sigma).toMonoidHom

abbrev fixedT (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Subgroup (fixedPGL n K sigma) :=
  (pslRange n K).subgroupOf (fixedPGL n K sigma)

instance fixedTNormal (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    (fixedT n K sigma).Normal := by
  change ((pslRange n K).comap (fixedPGL n K sigma).subtype).Normal
  infer_instance

@[expose] def fixedPSLMap (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    fixedPSL n K sigma →* fixedT n K sigma where
  toFun x := ⟨⟨ProjectiveSpecialLinearGroup.toPGL x.val, by
    change pglGraphFieldAut n K sigma (ProjectiveSpecialLinearGroup.toPGL x.val) =
      ProjectiveSpecialLinearGroup.toPGL x.val
    rw [← toPGL_pslGraphFieldAut]
    exact congrArg ProjectiveSpecialLinearGroup.toPGL x.property⟩, ⟨x.val, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul _ x.val y.val))

theorem fixedPSLMap_bijective (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Function.Bijective (fixedPSLMap n K sigma) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply ProjectiveSpecialLinearGroup.toPGL_injective
    exact congrArg (fun z : fixedT n K sigma => z.val.val) h
  · intro y
    obtain ⟨x, hx⟩ := y.property
    have hxfixed : pslGraphFieldAut n K sigma x = x := by
      apply ProjectiveSpecialLinearGroup.toPGL_injective
      rw [toPGL_pslGraphFieldAut, hx]
      exact y.val.property
    refine ⟨⟨x, hxfixed⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx

@[expose] def fixedPSLEquivT (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    fixedPSL n K sigma ≃* fixedT n K sigma :=
  MulEquiv.ofBijective (fixedPSLMap n K sigma) (fixedPSLMap_bijective n K sigma)


theorem pComponent_fixed_image (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (p : ℕ) (L : Subgroup (fixedPSL n K sigma))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p (L.map (fixedPSLEquivT n K sigma).toMonoidHom) :=
  CatalogueBAlternating.pComponent_map_equiv p (fixedPSLEquivT n K sigma) L hL

theorem pComponent_fixed_extend (n : ℕ) (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (p : ℕ) [Fact p.Prime] (L : Subgroup (fixedPSL n K sigma))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p
      ((L.map (fixedPSLEquivT n K sigma).toMonoidHom).map (fixedT n K sigma).subtype) :=
  CatalogueBAlternating.pComponent_of_normal_subgroup p (fixedT n K sigma)
    (L.map (fixedPSLEquivT n K sigma).toMonoidHom) (pComponent_fixed_image n K sigma p L hL)

end

end CFSG.ComponentClassification.CatalogueBGraphField
