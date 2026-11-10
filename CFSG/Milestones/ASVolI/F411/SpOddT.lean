module

public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut

public section

namespace CFSG.ASVolI

open Matrix Subgroup CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.AUTSL.SpTwo

variable {K : Type} [Field K]


theorem burnsideF411_spCoordImage_flag (σ : K ≃+* K) {i : ℕ} (hi : i ≤ 2) :
    spCoordImage σ (flag 2 K i) = flag 2 K i := by
  ext v
  rw [mem_spCoordImage, mem_flag_of_le hi, mem_flag_of_le hi, mem_isoFlag, mem_isoFlag]
  simp


end CFSG.ASVolI
