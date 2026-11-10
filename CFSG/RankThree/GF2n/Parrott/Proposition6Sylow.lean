module

public import CFSG.RankThree.GF2n.Parrott.Proposition6D8SquareOne
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5PermA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.OddStandard.SmallF3.HarrisU33
open CFSG.OddStandard.SmallF3.Omega
open CFSG.OddStandard.SmallF3.Omega.K5
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {z : G}

theorem card_inf_L1_L2 {L1 L2 : Subgroup G} (hL1 : Nonempty (↥L1 ≃* SL23))
    (hinf1 : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype) :
    Nat.card ((Subgroup.center L1).map L1.subtype) = 2 := by
  obtain ⟨e⟩ := hL1
  rw [Subgroup.card_subtype L1 (Subgroup.center L1)]
  exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans card_center_sl23_p6

theorem card_core
    {L1 L2 : Subgroup G}
    (hL1 : Nonempty (↥L1 ≃* SL23))
    (hL2 : Nonempty (↥L2 ≃* SL23))
    (hcomm : ∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x)
    (hinf1 : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype)
    (hsup : L1 ⊔ L2 = twoThreeCore (H z)) :
    Nat.card (twoThreeCore (H z)) = 288 := by
  classical
  have hcardL1 : Nat.card ↥L1 = 24 := by
    obtain ⟨e⟩ := hL1
    exact (Nat.card_congr e.toEquiv).trans card_sl23_p6
  have hcardL2 : Nat.card ↥L2 = 24 := by
    obtain ⟨e⟩ := hL2
    exact (Nat.card_congr e.toEquiv).trans card_sl23_p6
  have hcardZ : Nat.card ((Subgroup.center L1).map L1.subtype) = 2 :=
    card_inf_L1_L2 hL1 hinf1
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L1 L2 hcomm).1
  rw [hsup, hinf1, hcardZ, hcardL1, hcardL2] at hprod
  omega


end CFSG.RankThree.GF2n.Parrott
