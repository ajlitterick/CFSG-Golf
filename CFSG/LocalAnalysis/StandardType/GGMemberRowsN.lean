module

import CFSG.LocalAnalysis.StandardType.GGResidualRk1FrameHolds
import CFSG.LocalAnalysis.StandardType.GGResidualRk1ExcTops
import CFSG.LocalAnalysis.StandardType.GGResidualExcRows
import CFSG.LieType.Steinberg.CentralExt.TwistedE6ToralCoordsHolds

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE
public import CFSG.Sporadic.Co2Smith.GlC0MarkInputs
import Certificates.Kernel.Co2Smith.Cox
import Certificates.Data.Kernel.Co2Smith.Mark
import Certificates.Data.Kernel.Co2Smith.Cox
import Certificates.Kernel.Co2Smith.LettersData
import Certificates.Kernel.Co2Smith.CoxData
import Certificates.Kernel.Co2Smith.MarkK
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseEnnolaTwo
import CFSG.LocalAnalysis.StandardType.GGPairResidualUnitaryTwo
import CFSG.LocalAnalysis.StandardType.GGPairResidualOrthTwo
import CFSG.LocalAnalysis.StandardType.GGPairResidualE7Plus
import CFSG.LocalAnalysis.StandardType.GGPairResidualE8Plus
import CFSG.LocalAnalysis.StandardType.GGPairResidualTwE6Plus
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylInputHolds
public import CFSG.CGT.A8S.N0EnumInputs
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Sec5One
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral
public import CFSG.Certificates.Kernel.Census.SiftSound
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.LargeExtraspecial.AS62EnumInputs
public import CFSG.LargeExtraspecial.S10SixE
public import CFSG.LargeExtraspecial.S10SixF
public import CFSG.LargeExtraspecial.S10SixH
public import CFSG.LargeExtraspecial.S10SixI
public import CFSG.LargeExtraspecial.S10SixJ
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridgeBase
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.Sporadic.Co2Smith.CTree
public import CFSG.Sporadic.Co2Smith.HPExclude
public import CFSG.Sporadic.Co2Smith.HPTree
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMSU
public import CFSG.Timmesfeld.ARS.CaseMSpLevi
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Bridge.RootSetsGate
public import CFSG.Timmesfeld.Bridge.RootSetsSyl
public import CFSG.Timmesfeld.Exceptional.DeepFixed
public import CFSG.Timmesfeld.Exceptional.DeepJ2Split
public import CFSG.Timmesfeld.Exceptional.DeepW1
public import CFSG.Timmesfeld.Moufang.Three
public import Certificates.Data.CFSGNative.Co2Smith.Orbit8
public import Certificates.Data.E6TableT

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan

theorem ggSecFiveRk1PhanNInput_of_rows (hS : GGRk1SplitMemberInput) (hU : GGRk1UnitaryMemberInput)
    (hR : GGRk1ResidualMemberInput) : GGSecFiveRk1PhanNInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 _ X hX r hrA hrC
  by_cases hs : GGSplitLie p X
  · exact hS G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX hs r hrA hrC
  · by_cases hu : GGMemberUnitary p Bs X
    · exact hU G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX hs hu r hrA hrC
    · exact hR G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX hs hu r hrA hrC

theorem ggPairResidualMemberRestInput_of_residual (hR : GGPairResidualMemberInput) :
    GGPairResidualMemberRestInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 _ _ X hX hXs hXu _ _ r hrA hrC s hsA hsC hne
  exact hR G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX hXs hXu r hrA hrC s hsA hsC hne

section Orthogonal

theorem ggPairConcl_of_orthogonal_ge_four
    (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (𝒦 : Finset (Subgroup G))
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (_hns : ¬ GGSplitLie p L)
    (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (_hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (X : Subgroup G) (_hX : X = L ∨ X ∈ 𝒦)
    (_hXs : ¬ GGSplitLie p X) (_hXu : ¬ GGMemberUnitary p Bs X)
    (horth : GGInnerDiagOnLabel
      (fun p lab => (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n) p Bs X)
    (r : MulAut ↥Bs) (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e)
    (s : MulAut ↥Bs) (hsA : s ∈ ggAutomizer X Bs) (hsC : s ∈ ggCoxRefl M e)
    (hne : r ≠ s) : GGPairConcl Bs X r s := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsPerfect X := ⟨horth.1⟩
  have hZ : ∀ lab,
      (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → Subgroup.center ↥X = ⊥ := by
    intro lab hrow hhas
    have htag : lab.tag = .D ∨ lab.tag = .twD := by
      rcases hrow.1 with hplus | hminus
      · exact Or.inl hplus.1
      · exact Or.inr hminus.1
    have hrank : 4 ≤ lab.rank := by
      rcases hrow.1 with hplus | hminus
      · exact hplus.2.1
      · exact le_trans (by omega) hminus.2.1
    exact OrthTorus.center_eq_bot_of_hasLabel_orth htag hrank hrow.2 hhas
  exact OrthTorus.pair_of_orthogonal_marking ggLabelRigidInput_holds hp2
    (ggRouteCfg_isElemAbelian hcfg) hcfg.1.1.2.1.2.2.2 (fun _ hrow => hrow.1) horth hZ
    r s hrA hsA (ggCoxRefl_isReflection hpres.2 hrC)
    (ggCoxRefl_isReflection hpres.2 hsC) hne

theorem ggPairResidualMemberNInput_of_rest (hR : GGPairResidualMemberRestInput) :
    GGPairResidualMemberNInput := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hA hbig X hX hXs hXu r hrA hrC s hsA hsC hne
  by_cases horth : GGInnerDiagOnLabel
      (fun p lab => (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n) p Bs X
  · exact ggPairConcl_of_orthogonal_ge_four G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3
      X hX hXs hXu horth r hrA hrC s hsA hsC hne
  · have hLtwo : ¬ (X = L ∧ GGInnerDiagOnLabel
        (fun p lab => lab.n = 1 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab)) p Bs X) := by
      rintro ⟨rfl, htwo⟩
      exact NSJoin.false_of_orthTwo_L hcfg hpres hle3 hbig htwo
    exact hR G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hA hbig X hX hXs hXu horth hLtwo
      r hrA hrC s hsA hsC hne

end Orthogonal

theorem ggSecFivePhanPairNInput_of_rows (hU : GGPairUnitaryMemberInput)
    (hR : GGPairResidualMemberNInput) : GGSecFivePhanPairNInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hA hbig X hX hXs r hrA hrC r' hrA' hrC' hne
  by_cases hu : GGMemberUnitary p Bs X
  · exact hU G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX hXs hu r hrA hrC r' hrA' hrC' hne
  · exact hR G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hA hbig X hX hXs hu r hrA hrC r' hrA' hrC' hne

theorem ggSecFiveGenPhanNInput_of_rows (hL1 : GGSecFiveL1PhanInput)
    (hU : GGGenUnitaryMemberInput) (hR : GGGenResidualMemberInput) : GGSecFiveGenPhanNInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 _ hbig X hX hXs
  by_cases hu : GGMemberUnitary p Bs X ∧ GGMemberUnitary p Bs L
  · exact hU hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig X hX hXs hu.1 hu.2
  · exact hR G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig X hX hXs hu

theorem ggSecFiveRk1PhanInput_of_rows (hS : GGRk1SplitMemberInput) (hU : GGRk1UnitaryMemberInput)
    (hR : GGRk1ResidualMemberInput) : GGSecFiveRk1PhanInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX r hrA hrC
  by_cases hs : GGSplitLie p X
  · exact hS G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX hs r hrA hrC
  · by_cases hu : GGMemberUnitary p Bs X
    · exact hU G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX hs hu r hrA hrC
    · exact hR G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX hs hu r hrA hrC

end CFSG.StandardType

end
