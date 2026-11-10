module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Comp
public import CFSG.Blueprint.Chevalley
import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoPlumb
import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoRat
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HF4Model
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeExcE678
import CFSG.LocalAnalysis.SeitzReduction.E8PilotAutD
import CFSG.GroupTheory.InnerNormalizedAutomorphisms
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TriD4

open CFSG.Open CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup b3Lie_fixSubgroup_conj)

theorem componentsNoD4_adjointGroup
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {α : MulAut ↥(adjointGroup τ K)} (hα3 : α ^ 3 = 1) :
    ComponentsNoD4 α := by
  intro I hI
  obtain ⟨s, hs⟩ : ∃ s, α = MulAut.conj s := by
    rcases hτ with rfl | rfl | rfl | rfl
    · exact CFSG.LocalAnalysis.GLTheoremA.CatB.I2610.exists_eq_conj_of_pow_three_F4 hK hα3
    · exact CFSG.LocalAnalysis.GLTheoremA.T171S.exists_eq_conj_of_pow_three_E6 hK hα3
    · exact CFSG.SeitzReduction.E8Pilot.exists_eq_conj_of_card_eq_two (Or.inl rfl) hK α
    · exact CFSG.SeitzReduction.E8Pilot.exists_eq_conj_of_card_eq_two (Or.inr rfl) hK α
  have hrat : CFSG.StandardType.ExcThreeTwoRatNotExc τ := by
    rcases hτ with rfl | rfl | rfl | rfl
    exacts [CFSG.StandardType.excThreeTwoRatNotExc_F4, CFSG.StandardType.excThreeTwoRatNotExc_E6,
      CFSG.StandardType.excThreeTwoRatNotExc_E7, CFSG.StandardType.excThreeTwoRatNotExc_E8]
  have hcomp := CFSG.StandardType.ExcThreeAtTwo.centCompNotExcThreeAt_three_adjointGroup hτ hrat hK
  have hs3 : s ^ 3 = 1 := by
    have hconj : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, ← hs, hα3]
    have hmem := CFSG.InnerNormalizedAutomorphisms.mem_center_of_conj_eq_one hconj
    rwa [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hmem
  rw [hs, b3Lie_fixSubgroup_conj] at hI
  exact (hcomp s hs3 I (CFSG.Assembly.isComponentOf_iff_open.mpr hI)).1

end CFSG.LocalAnalysis.GLTheoremA.TriD4

end
