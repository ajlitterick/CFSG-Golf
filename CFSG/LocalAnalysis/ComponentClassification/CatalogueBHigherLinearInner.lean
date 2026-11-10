module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerParameters
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionComponents

public section

namespace CFSG.ComponentClassification.CatalogueBHigherLinearInner

noncomputable section

open CatalogueBHigherLinearAction

universe u

theorem innerDiagonal_involution_fixed_pComponent_quasisimple
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 2 ≤ n) (hodd : Odd (Nat.card K))
    (hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hne : innerDiagonalAction n K A ≠ 1)
    (hsq : innerDiagonalAction n K A ^ 2 = 1)
    (p : ℕ) (hp : p.Prime)
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup (innerDiagonalAction n K A)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨ha, ha2, _⟩ := inner_involution_projective_data n K hn hparameter A hne hsq
  let a := Matrix.ProjGenLinGroup.mk A
  let e := fixedPSLCentralizerEquiv n K a
  let M := L.map e.toMonoidHom
  have hcomponent := pComponent_fixed_extend n K a p L hL
  have hquasi := CatalogueBProjectiveInvolution.projective_involution_centralizer_pComponent_quasisimple
    n hn A (Ring.two_ne_zero (ringChar_ne_two_of_odd_card K hodd)) ha ha2 p hp
    (M.map (localPSLRange n K a).subtype) hcomponent
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv
      ((L.equivMapOfInjective e.toMonoidHom e.injective).trans
        (M.equivMapOfInjective (localPSLRange n K a).subtype
          (localPSLRange n K a).subtype_injective))
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))


end

end CFSG.ComponentClassification.CatalogueBHigherLinearInner
