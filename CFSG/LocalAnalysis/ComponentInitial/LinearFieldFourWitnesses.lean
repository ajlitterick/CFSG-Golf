module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourCover
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourConjugacy

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFieldFour

open Subgroup Matrix LinearFlag CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

theorem pslModel_eq_range_toPGL (n p f : ℕ) [Fact p.Prime] :
    Assembly.ComponentType.pslModel n p f =
      (SpecialLinearGroup.toPGL :
        SpecialLinearGroup (Fin n) (GaloisField p f) →* ProjGenLinGroup (Fin n) _).range := by
  rw [Assembly.ComponentType.pslModel, PGLModel.projSL, PGLModel.projImage,
    SpecialLinearGroup.toPGL, MonoidHom.range_comp, SpecialLinearGroup.range_toGL_eq_ker_det]

@[expose] def pslModelEquivProjectiveSL (n p f : ℕ) [Fact p.Prime] :
    Assembly.ComponentType.pslModel n p f ≃* projectiveSL n (GaloisField p f) :=
  ((QuotientGroup.quotientMulEquivOfEq
      (by rw [SpecialLinearGroup.toPGL_ker, scalars_eq_center] :
        scalars n (GaloisField p f) = (SpecialLinearGroup.toPGL :
          SpecialLinearGroup (Fin n) (GaloisField p f) →* ProjGenLinGroup (Fin n) _).ker)).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (pslModel_eq_range_toPGL n p f).symm))).symm

theorem card_galoisField_two_two : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num


end LinearFieldFour

end CFSG.LocalAnalysis.ComponentInitial
