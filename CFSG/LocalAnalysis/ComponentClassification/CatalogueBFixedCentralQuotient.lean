module

public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientAlgebra
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotient

public section

namespace CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

variable {X : Type*} [Group X] [Finite X]

theorem fixedImage_pComponent_quasisimple (Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center X) (ψ : MulAut X)
    (hinvariant : Z.map ψ.toMonoidHom = Z)
    (p : ℕ) [Fact p.Prime]
    (hfixed : ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup ψ),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L)
    (M : Subgroup (fixedImage Z ψ hinvariant)) (hM : CFSG.IsPComponent p M) :
    CFSG.IsQuasisimple M := by
  let f := fixedImageProjection Z ψ hinvariant
  have hsurjective := fixedImageProjection_surjective Z ψ hinvariant
  have hkernel := fixedImageProjection_kernel_central Z ψ hinvariant hcentral
  obtain ⟨L, hL, hmap, _⟩ :=
    CatalogueBCentralQuotient.pComponent_exists_lift p f hsurjective hkernel M hM
  rw [← hmap]
  exact (CatalogueBCentralQuotient.pComponent_quasisimple_iff f hkernel p L hL).mp
    (hfixed L hL)

theorem quotientFixed_pComponent_quasisimple (Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center X) (ψ : MulAut X)
    (hinvariant : Z.map ψ.toMonoidHom = Z)
    (p : ℕ) [Fact p.Prime]
    (hfixed : ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup ψ),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L)
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let := fixedImage_normal Z ψ hinvariant hcentral
  let := fixed_quotient_abelian Z ψ hinvariant hcentral
  exact pComponent_quasisimple_of_normal_solvable_quotient p (fixedImage Z ψ hinvariant)
    (fixedImage_pComponent_quasisimple Z hcentral ψ hinvariant p hfixed) L hL

theorem central_quotient_fixed_p_component_transfer (Z : Subgroup X)
    (hcentral : Z ≤ Subgroup.center X) (ψ : MulAut X)
    (hinvariant : Z.map ψ.toMonoidHom = Z) :
    letI := Subgroup.normal_of_le_center hcentral
    (fixedImage Z ψ hinvariant).Normal ∧
      (letI := fixedImage_normal Z ψ hinvariant hcentral;
        IsMulCommutative
          ((FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant)) ⧸
            fixedImage Z ψ hinvariant)) ∧
      Function.Surjective (fixedImageProjection Z ψ hinvariant) ∧
      (fixedImageProjection Z ψ hinvariant).ker =
        Z.subgroupOf (FixedCommutingProduct.fixedSubgroup ψ) ∧
      (fixedImageProjection Z ψ hinvariant).ker ≤
        Subgroup.center (FixedCommutingProduct.fixedSubgroup ψ) ∧
      (∀ p : ℕ, p.Prime →
        (∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup ψ),
          CFSG.IsPComponent p L → CFSG.IsQuasisimple L) →
        ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant)),
          CFSG.IsPComponent p L → CFSG.IsQuasisimple L) := by
  let := Subgroup.normal_of_le_center hcentral
  refine ⟨fixedImage_normal Z ψ hinvariant hcentral,
    fixed_quotient_abelian Z ψ hinvariant hcentral,
    fixedImageProjection_surjective Z ψ hinvariant,
    fixedImageProjection_kernel Z ψ hinvariant,
    fixedImageProjection_kernel_central Z ψ hinvariant hcentral, ?_⟩
  intro p hp hfixed L hL
  let : Fact p.Prime := ⟨hp⟩
  exact quotientFixed_pComponent_quasisimple Z hcentral ψ hinvariant p hfixed L hL


end CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
