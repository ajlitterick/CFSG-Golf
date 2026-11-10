module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSL
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraphExc
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraphSp
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraphSU
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraphTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

section Assembly

theorem ggOrdPGraphAt_of_orthogonal (hP : GGOrdPGraphAt .POmegaPlus)
    (hM : GGOrdPGraphAt .POmegaMinus) : ∀ t, GGOrdPGraphAt t := by
  intro t
  cases t with
  | PSL => exact ggOrdPGraphAt_PSL
  | PSU => exact ggOrdPGraphAt_PSU
  | PSp => exact ggOrdPGraphAt_PSp
  | POmegaOdd => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])
  | POmegaPlus => exact hP
  | POmegaMinus => exact hM
  | G2 => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])
  | F4 => exact ggOrdPGraphAt_F4
  | E6 => exact ggOrdPGraphAt_E6
  | E7 => exact ggOrdPGraphAt_E7
  | E8 => exact ggOrdPGraphAt_E8
  | twistedE6 => exact ggOrdPGraphAt_twistedE6
  | trialityD4 => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])
  | twistedB2 => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])
  | twistedG2 => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])
  | twistedF4 => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])
  | Tits => exact ggOrdPGraphAt_of_small (by simp [GGOrdPSmallTag])


end Assembly

end CFSG.StandardType
