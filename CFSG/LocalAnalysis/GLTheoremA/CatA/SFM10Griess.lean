module

public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.Models
public import CFSG.Open.StatedDefs
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM10

open CFSG.Open

theorem natCard_multiplicative_zmod (n : ℕ) : Nat.card (Multiplicative (ZMod n)) = n := by
  rw [← Nat.card_congr Multiplicative.ofAdd, Nat.card_zmod]

section Griess


theorem card_center_dvd_two {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 27)
    (e : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSp 2 K)) :
    Nat.card (Subgroup.center Q) ∣ 2 := by
  classical
  haveI : Group.IsPerfect Q := ⟨hQ.1⟩
  have hadm : CFSG.Open.StatedLieAdmissible CFSG.Open.StatedLieTag.PSp 2 3 3 :=
    ⟨Nat.prime_three, by norm_num, by norm_num, by decide⟩
  have hK3 : Nat.card K = 3 ^ 3 := by rw [hK]; norm_num
  have hcm : CFSG.Open.StatedClassicalModel (Q ⧸ Subgroup.center Q) CFSG.Open.StatedLieTag.PSp 2 3 3 :=
    ⟨hadm, K, inferInstance, inferInstance, hK3, ⟨e⟩⟩
  have hmod : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) CFSG.Open.StatedLieTag.PSp 2 3 3 :=
    ⟨hadm, Or.inl hcm⟩
  obtain ⟨-, ⟨φ⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models
    (Q ⧸ Subgroup.center Q) CFSG.Open.StatedLieTag.PSp 2 3 3 hmod
  have hgen : CFSG.Blueprint.Multiplier.genericOrders CFSG.Open.StatedLieTag.PSp 2 3 3 = (2, 1) := by
    norm_num [CFSG.Blueprint.Multiplier.genericOrders]
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders CFSG.Open.StatedLieTag.PSp 2 3 3 = (1, 1) :=
    rfl
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (Q ⧸ Subgroup.center Q)) = 2 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod]
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hgen, hexc,
      Nat.card_prod, natCard_multiplicative_zmod]
  have hfin : Finite (CFSG.Open.griessHopfMultiplier (Q ⧸ Subgroup.center Q)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let q : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker ≤ Subgroup.center Q := (QuotientGroup.ker_mk' _).le
  let ψ : CFSG.Open.griessHopfMultiplier (Q ⧸ Subgroup.center Q) →* q.ker :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hq hker).comp
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toMonoidHom
  have hψ : Function.Surjective ψ :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq hker).comp
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).surjective
  have hdvd := Subgroup.card_dvd_of_surjective hψ
  rw [hcard] at hdvd
  have hk : q.ker = Subgroup.center Q := QuotientGroup.ker_mk' _
  rw [hk] at hdvd
  exact hdvd

end Griess

end CFSG.LocalAnalysis.GLTheoremA.SFM10

end
