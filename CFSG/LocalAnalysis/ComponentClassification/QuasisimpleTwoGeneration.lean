module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.Open.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LocalAnalysis.ComponentClassification.Layer
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.TwoResidual
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

open CFSG.Open

namespace CFSG.ComponentClassification.QuasisimpleTwoGeneration


theorem residual_eq_top_of_corefree {G : Type*} [Group G] [Finite G]
    (hquasisimple : IsQuasisimple G) (hcorefree : componentClassificationOddCore G = ⊥) :
    TwoResidual.subgroup G = ⊤ := by
  let : (TwoResidual.subgroup G).Characteristic := TwoResidual.characteristic G
  rcases Quasisimple.normal_le_center_or_eq_top hquasisimple (TwoResidual.subgroup G) with
    hcentral | htop
  · let : Group.IsPerfect G := ⟨hquasisimple.1⟩
    let : Nontrivial G := Quasisimple.nontrivial hquasisimple
    let sylow : Sylow 2 G := Classical.choice inferInstance
    have hsylowCentral : (sylow : Subgroup G) ≤ Subgroup.center G :=
      (TwoResidual.twoSubgroup_le _ sylow.isPGroup').trans hcentral
    let : IsMulCommutative (sylow : Subgroup G) := isMulCommutative_iff.mpr
      fun left right => Subtype.ext
        ((Subgroup.mem_center_iff.mp (hsylowCentral left.property)) right).symm
    have hnormalizer : Subgroup.normalizer (sylow : Set G) ≤
        Subgroup.centralizer (sylow : Set G) := by
      intro element _
      apply Subgroup.mem_centralizer_iff.mpr
      intro member hmember
      exact ((Subgroup.mem_center_iff.mp (hsylowCentral hmember)) element).symm
    let transfer := MonoidHom.transferSylow sylow hnormalizer
    have htransfer : transfer = 1 := PerfectAutomorphisms.hom_eq_one_of_commutative transfer
    have hkernel : transfer.ker = ⊤ := MonoidHom.ker_eq_top_iff.mpr htransfer
    have hnotTwo : ¬ 2 ∣ Nat.card G := by
      have hnot := MonoidHom.not_dvd_card_ker_transferSylow sylow hnormalizer
      change ¬ 2 ∣ Nat.card transfer.ker at hnot
      simpa only [hkernel, Subgroup.card_top] using hnot
    have hodd : Odd (Nat.card G) := Nat.coprime_two_left.mp
      (Nat.prime_two.coprime_iff_not_dvd.mpr hnotTwo)
    have hcoreTop : (⊤ : Subgroup G) ≤ componentClassificationOddCore G :=
      OddCore.maximal G ⊤ inferInstance (by simpa only [Subgroup.card_top] using hodd)
    rw [hcorefree] at hcoreTop
    exact (not_le_of_gt (bot_lt_top : (⊥ : Subgroup G) < ⊤) hcoreTop).elim
  · exact htop


end CFSG.ComponentClassification.QuasisimpleTwoGeneration
