module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront78Nar
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F08

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]


end CFSG.LocalAnalysis.UniquenessCase.UC22.F08

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem uniqueMax_of_two_le_pRank_sigma (hU : uniqueFourUnique G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) {p : ℕ} (hp : p ∈ uniqueFourSigma M) {L : Subgroup G}
    (hLM : L ≤ M) (h2 : 2 ≤ CFSG.Open.pRank p L) : UniqueMax M L := by
  show calMOf L = {M}
  ext N
  constructor
  · rintro ⟨hN, hLN⟩
    have hle := sec61 hU hM hp hLM h2 hN.1 hLN
    exact (hN.2 _ hM.1 hle).symm
  · intro hN
    have hNM : N = M := hN
    subst hNM
    exact ⟨hM, hLM⟩


end CFSG.LocalAnalysis.UniquenessCase.UC6
