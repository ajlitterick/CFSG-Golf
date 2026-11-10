module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCSpecA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Pocket
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ComponentClassification.HarrisLit.P1 Certificates.Asc82Fbar

variable {n : ℕ}

theorem slList_complete : ∀ A : SL2F3, A ∈ slList () := by decide +kernel

theorem slCode_lt (A : SL2F3) : slCode A < 81 := by
  have h1 := ZMod.val_lt (A.1 0 0)
  have h2 := ZMod.val_lt (A.1 0 1)
  have h3 := ZMod.val_lt (A.1 1 0)
  have h4 := ZMod.val_lt (A.1 1 1)
  unfold slCode
  omega


end CFSG.OddStandard.SmallF3.Omega
