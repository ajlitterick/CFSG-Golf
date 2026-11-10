module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormParameters
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInner

public section

namespace CFSG.ComponentClassification.CatalogueBGraphForm

noncomputable section

open CatalogueBHigherLinearAction

universe u

theorem similitude_pComponent_quasisimple_of_isometries
    (n : ℕ) (K : Type u) [Field K] [Finite K] [Nonempty (Fin n)]
    (R : Matrix.GeneralLinearGroup (Fin n) K) (p : ℕ) [Fact p.Prime]
    (hI : ∀ J : Subgroup (isometryGroup n K R),
      CFSG.IsPComponent p J → CFSG.IsQuasisimple J)
    (L : Subgroup (similitudeGroup n K R)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L := by
  apply CatalogueBFixedCentralQuotient.pComponent_quasisimple_of_normal_solvable_quotient
    p (isometryInSimilitude n K R) _ L hL
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (isometryInSimilitudeEquiv n K R) hI

theorem fixedPGL_pComponent_quasisimple_of_isometries
    (n : ℕ) (K : Type u) [Field K] [Finite K] [Nonempty (Fin n)]
    (A : Matrix.GeneralLinearGroup (Fin n) K) (p : ℕ) [Fact p.Prime]
    (hI : ∀ J : Subgroup (isometryGroup n K A⁻¹),
      CFSG.IsPComponent p J → CFSG.IsQuasisimple J)
    (L : Subgroup (fixedPGL n K A)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L :=
  CatalogueBProjectiveInvolution.pComponent_quasisimple_of_central_surjection p
    (similitudeProjection n K A) (similitudeProjection_surjective n K A)
    (similitudeProjection_central_kernel n K A)
    (similitude_pComponent_quasisimple_of_isometries n K A⁻¹ p hI) L hL

theorem fixedPSL_pComponent_quasisimple_of_isometries
    (n : ℕ) (K : Type u) [Field K] [Finite K] [Nonempty (Fin n)]
    (A : Matrix.GeneralLinearGroup (Fin n) K) (p : ℕ) [Fact p.Prime]
    (hI : ∀ J : Subgroup (isometryGroup n K A⁻¹),
      CFSG.IsPComponent p J → CFSG.IsQuasisimple J)
    (L : Subgroup (fixedPSL n K A)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L := by
  let e := fixedPSLEquivT n K A
  let M := L.map e.toMonoidHom
  have hextend := pComponent_fixed_extend n K A p L hL
  have hquasi := fixedPGL_pComponent_quasisimple_of_isometries n K A p hI
    (M.map (fixedT n K A).subtype) hextend
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv
      ((L.equivMapOfInjective e.toMonoidHom e.injective).trans
        (M.equivMapOfInjective (fixedT n K A).subtype (fixedT n K A).subtype_injective))
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

theorem pure_graph_fixed_components_form_reduction
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 3 ≤ n) (hodd : ringChar K ≠ 2)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (_hne : pureGraphAction n K A ≠ 1) (hsq : pureGraphAction n K A ^ 2 = 1) :
    (A.val.transpose = A.val ∨ (A.val.transpose = -A.val ∧ Even n)) ∧
      ∀ (p : ℕ), p.Prime →
        (∀ J : Subgroup (isometryGroup n K A⁻¹),
          CFSG.IsPComponent p J → CFSG.IsQuasisimple J) →
        ∀ L : Subgroup (fixedPSL n K A), CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  refine ⟨pureGraph_involution_form_data n K hn hodd A hsq, ?_⟩
  intro p hp hI L hL
  let : Fact p.Prime := ⟨hp⟩
  exact fixedPSL_pComponent_quasisimple_of_isometries n K A p hI L hL


end

end CFSG.ComponentClassification.CatalogueBGraphForm
