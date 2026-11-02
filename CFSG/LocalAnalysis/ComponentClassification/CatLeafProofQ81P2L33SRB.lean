module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCommon
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseBabySchreier
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.B.CTIB.CoreCensus
public import CFSG.Monster.B.CTIB.Rank2158
public import CFSG.Monster.B.CTIB.Rank2158Witness
public import CFSG.Monster.B.CTIB.DistThreeProductFinal
public import CFSG.Monster.B.GSide.HInnerFusion
public import CFSG.Monster.B.Cbar.Simple
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Leaf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC311a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitCor441
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Count
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Fbar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitProperComplete
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.CTIB
open CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.ComponentClassification.BMCase

theorem not_isPGroup_jbar_centralizer
    [Finite Sbp] (t : Sbp) {k : ℕ}
    (hk : (jClass t).ncard = k) (hk0 : 0 < k) (h3 : 3 ∣ 2 ^ 41 * 161382375 / k) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set Sbp)) := by
  have hcl : CFSG.Sporadic.Schreier.conjClass Jbar.op t = jClass t := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c⁻¹, Jbar.op.inv_mem hc, by group⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g⁻¹, Jbar.op.inv_mem hg, by group⟩
  have h := CFSG.Sporadic.Schreier.ncard_conjClass_mul_card Jbar.op t
  rw [hcl, hk, GSide.natCard_Jbar_op] at h
  refine not_isPGroup_of_le (inf_le_right : Jbar.op ⊓ centralizer {t} ≤ centralizer {t})
    (not_isPGroup_of_three_dvd ?_)
  change 3 ∣ Nat.card ↥(CFSG.Sporadic.Schreier.centralizerIn Jbar.op t)
  have h' : Nat.card ↥(CFSG.Sporadic.Schreier.centralizerIn Jbar.op t) =
      2 ^ 41 * 161382375 / k := by
    rw [← h, Nat.mul_div_cancel_left _ hk0]
  rw [h']
  exact h3

theorem sporNoTwoFix_B
    : SporNoTwoFix .B := by
  obtain ⟨hfin, -, hsC, m, hm, hcard⟩ := short_centralizer_generated_quotient_simple
  have : Finite Sbp := Finite.of_injective _ (MulEquiv.inv' Cbar).symm.injective
  have hsS : IsSimpleGroup Sbp := @MulEquiv.isSimpleGroup _ _ _ _ hsC (MulEquiv.inv' Cbar).symm
  have hZ : center Sbp = ⊥ := by
    refine center_eq_bot_of_not_prime hsS
      ((Nat.card_congr (MulEquiv.inv' Cbar).toEquiv).symm.trans hcard) fun hp => ?_
    have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (dvd_mul_of_dvd_left (dvd_pow_self 2 (by norm_num)) m)
    have h4 : 4 ∣ 2 ^ 41 * m := dvd_mul_of_dvd_left (pow_dvd_pow 2 (by norm_num : 2 ≤ 41)) m
    rw [← h2] at h4
    norm_num at h4
  let eP : NativeSporadic.Carrier .B ≃* Sbp :=
    nonempty_pinnedB_equiv_Cbar.some.trans (MulEquiv.inv' Cbar)
  refine sporNoTwoFix_of_mulEquiv eP
    (forall_of_inner_reps hZ (fun α => ?_) [rs 1, rs 0, rs 5, rs 3] (fun t ht => ?_) ?_)
  · obtain ⟨g, hg⟩ := inner_of_mulEquiv_pinnedB Sbp ⟨eP.symm⟩ α
    exact ⟨g, hg.symm⟩
  · obtain ⟨i, ⟨hi, hti⟩, -⟩ := four_classes CFSG.Sporadic.Co2Inv.co2_involution_input ht
    refine ⟨rs i, ?_, hti.symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    rcases hi with rfl | rfl | rfl | rfl <;> simp
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact not_isPGroup_jbar_centralizer _ ncard_jClass_rs1 (by norm_num) (by norm_num)
    · exact not_isPGroup_jbar_centralizer _ ncard_jClass_rs0 (by norm_num) (by norm_num)
    · obtain ⟨v, u, hvu, hd⟩ := exists_witness_pair ambientRootOrbitsHyp
      have hC := (distance_three_product_full_centralizer_final hvu rfl rfl rfl).2.2.2.2.2.1
      let Ψ : centralizer ({rs 6 * e2158} : Set Sbp) ≃*
          centralizer ({clabelS v * clabelS u} : Set Shat) :=
        (centralizerEquiv sEquiv (rs 6 * e2158)).trans (MulEquiv.subgroupCongr
          (congrArg (fun y : Shat => centralizer {y}) hd.symm))
      exact not_isPGroup_centralizer_of_isConj isConj_rs6_mul_e2158
        (not_isPGroup_of_mulEquiv Ψ (not_isPGroup_of_three_dvd (by rw [hC]; norm_num)))
    · exact not_isPGroup_jbar_centralizer _ ncard_jClass_rs3 (by norm_num) (by norm_num)

end CFSG.ComponentClassification.HarrisLit.L33.SR
