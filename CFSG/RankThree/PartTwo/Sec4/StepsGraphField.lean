module

public import CFSG.RankThree.PartTwo.KFacts.AutPSL
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourKernelGraph
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.KFacts Matrix

variable {k : Type*} [Field k]

theorem dualAut_ne_one [Finite k] {n : ℕ} (hn : 3 ≤ n) : dualAut n k ≠ 1 := fun h =>
  ProjectivePlane.dualAut_not_mem_semilinearAutGroup hn (h ▸ one_mem _)

theorem fieldAut_ne_one [Finite k] {n : ℕ} (hn : 3 ≤ n) {σ : k ≃+* k} (hσ : σ ≠ 1) :
    fieldAut n k σ ≠ 1 := fun h =>
  hσ (eq_one_of_conjAut_mul_fieldAut_eq_one hn 1 σ (by rw [map_one, one_mul, h])).1

theorem isGraphField_dualAut_mul_fieldAut [Finite k] {n : ℕ} (hn : 3 ≤ n) {σ : k ≃+* k}
    (hσ : σ ≠ 1) : (stdPinnedPSL n k).IsGraphField (dualAut n k * fieldAut n k σ) :=
  PinnedAut.isGraphField_of_mem _ (Set.mem_singleton _) (dualAut_ne_one hn) ⟨σ, rfl⟩
    (fieldAut_ne_one hn hσ)


end CFSG.RankThree.PartTwo.Sec4
