module

public import CFSG.OddTranspositions.PartThree.Nine.Statements
public import CFSG.LargeExtraspecial.S111SHCor3
public import CFSG.Holt.PointHullTwoGroupBasic
public import CFSG.Goldschmidt.Final
public import CFSG.CharacterTheory.Wreathed.NonabelianCentralizer
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Holt.Centralizer
public import CFSG.Holt.MaximalFixer
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.StronglyEmbedded
public import CFSG.Walter.JRFacts

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Open CFSG.Holt.PointHull


theorem isBenderGroup_of_wcl_abelian {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (P : Sylow 2 X) {t : X} (htP : t ∈ (P : Subgroup X))
    (ht1 : t ≠ 1) (htc : ∀ x ∈ (P : Subgroup X), x * t = t * x)
    (hab : IsMulCommutative (CFSG.LargeExtraspecial.S11.wcl t))
    (h16 : 16 ≤ Nat.card (P : Subgroup X)) : CFSG.BenderSuzuki.IsBenderGroup X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hcl⟩ := CFSG.LargeExtraspecial.S11.wcl_stronglyClosed P htP htc hab
  have hA : CFSG.LargeExtraspecial.S11.wcl t ≠ ⊥ := fun h => ht1 (by
    have ht := CFSG.LargeExtraspecial.S11.self_mem_wcl t
    rwa [h, Subgroup.mem_bot] at ht)
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  have h2 : Even (Nat.card X) := by
    refine even_iff_two_dvd.mpr ((?_ : 2 ∣ Nat.card (P : Subgroup X)).trans
      (Subgroup.card_subgroup_dvd_card _))
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨-, -, hc⟩ := CFSG.Goldschmidt.coreStatement X P _ hle hab hcl
    (normalClosure_eq_top hA) (goldschmidtOddCore_eq_bot h2)
  have hX := goldschmidtSimpleType_of_top hnonab (hc ⊤ (isComponentOf_top hnonab))
  rcases fusionIsBenderGroup_or_card_dvd hX with hB | ⟨k, hk, hdvd⟩
  · rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact .isPSL2 f hf e
    · exact .isPSU3 f hf
        (e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 f).symm))
    · exact .isSuzuki a ha
        (e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz a).symm))
  · exfalso
    have h8 := card_dvd_eight_of_isPGroup hk hdvd P.isPGroup'
    have := Nat.le_of_dvd (by norm_num) h8
    omega

end CFSG.OddTranspositions.PartThree.Nine
