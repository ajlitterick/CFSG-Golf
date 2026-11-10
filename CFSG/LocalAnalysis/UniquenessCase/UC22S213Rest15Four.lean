module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15NormFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15NonNormal

import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive





public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)






theorem s21_3Rest15_dataOfSetup4
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    S21_3Rest15 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) := by
  have hNorm := rest15Norm_dataOfSetup4 hS hU S hMS hPart
  have hCov := rest15Covers_dataOfSetup4_proved hS hU S hMS hPart
  have hCenter := rest15Center_dataOfSetup4_proved hS hU S hMS hPart
  have hModels := rest15Models_dataOfSetup4_proved hS hU S hMS hPart
  intro hH c L hL hC hC2 hCZ hCovEx hSp hL2 hT hSmall hlist hnn hU3 hTL hT4 hCh hU54 hY
    hthin h3 hk1 a ha hpr hN
  have hcover := rest15_coverage CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
    hL hC hC2 hCZ hSp hL2 hT hSmall hlist hU3 hTL hT4 hCh hU54 hY h3
  by_cases hNormal : (UC6.dataOfSetup4 hS hU S).M ≤ normalizer (L : Set G)
  · exact hNorm hH c L hL hC hC2 hCZ hCovEx hSp hL2 hT hSmall hlist hnn hU3 hTL hT4 hCh hU54
      hY hthin h3 hk1 hNormal a ha hpr hN
  by_cases hFive : FiveCovers (Bar2 L)
  · exact hCov hH c L hL hC hC2 hCZ hCovEx hSp hL2 hT hSmall hlist hnn hU3 hTL hT4 hCh hU54
      hY hthin h3 hk1 hNormal hFive a ha hpr hN
  by_cases hZ : 3 ∣ Nat.card (center (Bar2 L))
  · exact hCenter hH c L hL hC hC2 hCZ hCovEx hSp hL2 hT hSmall hlist hnn hU3 hTL hT4 hCh hU54
      hY hthin h3 hk1 hNormal hFive hZ a ha hpr hN
  have hModel := ((hcover.resolve_left hNormal).resolve_left hFive).resolve_left hZ
  exact hModels hH c L hL hC hC2 hCZ hCovEx hSp hL2 hT hSmall hlist hnn hU3 hTL hT4 hCh hU54
    hY hthin h3 hk1 hNormal hFive hZ hModel a ha hpr hN

end CFSG.LocalAnalysis.UniquenessCase.UC22
