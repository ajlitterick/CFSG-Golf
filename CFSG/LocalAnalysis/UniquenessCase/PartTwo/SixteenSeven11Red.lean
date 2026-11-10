module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Ctx
public import CFSG.LocalAnalysis.WeakClosure81.EightFour
public import CFSG.HardMathSupport.Solomon.Coordinator.B0TSylow
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.TwoGroupNormalizerMaxLocal.TwoGroupNormalizerMaxLocal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.RankThreeUC.SourceSetting
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1611_normalizer_le_of_noncyclic (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {X : Subgroup G}
    (hXM : X ≤ D.M) (hXp : IsPGroup p X) (hXc : ¬ IsCyclic X)
    (hXW : X ≤ normalizer (E3.wClos V 0 D.T : Set G)) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hVT : V ≤ D.T := TwelveTwentyTwo.le_T_of_hyp125 h
  have hVW : V ≤ E3.wClos V 0 D.T := by
    rw [wClos_zero_eq_iSup hV]
    exact le_iSup₂_of_le (1 : G) (by rwa [conjSubgroup_one]) (by rw [conjSubgroup_one])
  have hne : E3.wClos V 0 D.T ≠ ⊥ := fun hbot =>
    h.inCalV.1 (le_bot_iff.1 (hbot ▸ hVW))
  have h2 : IsPGroup 2 (E3.wClos V 0 D.T) :=
    IsPGroup.to_le (TwelveTwentyTwo.isPGroup_T D) (wClos_zero_le V D.T)
  exact TwoGroupNormalizerMaxLocal.normalizer_le_of_maxTwoLocalsContaining_eq_singleton hne h2
    hXW (h61 p hp X hXM hXp hXc)


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
