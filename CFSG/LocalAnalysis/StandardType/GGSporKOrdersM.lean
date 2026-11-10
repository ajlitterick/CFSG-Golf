module

public import CFSG.Sporadic.Bridge.MonsterModels
public import CFSG.Open.MonsterY443Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Fi23.StarKernel

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Blueprint

theorem ggSporK_card_sporadicM
    : Nat.card (TauCeti.CFSGIndex.sporadic .M).Group =
      808017424794512875886459904961710757005754368000000000 := by
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  have h := Nat.card_congr
    ((CFSG.Blueprint.NativeSporadic.MonsterModel.y443DerivedEquivOpen.symm.trans e).toEquiv)
  have h2 : Nat.card (TauCeti.CFSGIndex.sporadic .M).Group =
      Nat.card CFSG.Open.MonsterY443Derived := h.symm
  rw [h2, CFSG.Open.Open.monster_y443_derived_card]
  norm_num [CFSG.Open.monsterOrder]

end CFSG.StandardType.SporadicShape
