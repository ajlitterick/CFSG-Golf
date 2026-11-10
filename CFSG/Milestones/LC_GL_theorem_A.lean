module

public import Mathlib
public import CFSG.Open.Catalog
public import CFSG.Open.Defs
public import CFSG.Open.GLADefs
public import CFSG.Sporadic.Schreier.LyCheckSep
public import CFSG.Sporadic.Ly.KeySpec
public import CFSG.Sporadic.He.FpSpec
import Certificates.Kernel.SporSch.Ly.SepGlue
public import CFSG.Monster.Existence.StdOdd.Defs
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertLie
public import CFSG.LieType.Chevalley.C2E6StdMatrixData
public import CFSG.Monster.B.Classical.E6AdjointGroup
import Certificates.Kernel.Misc.E6StdSlp
public import CFSG.YGroups.Y443.Native.CoverFactsWords
import Certificates.Kernel.KDense.Y443
public import CFSG.YGroups.Y443.Native.Swap13Word
public import CFSG.Sporadic.Ly.FiveFacts
import CFSG.Sporadic.Ly.Certificate
public import CFSG.Sporadic.Ly.Setup
import CFSG.Sporadic.Ly.GenSpecBase
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.ThreeBData
public import CFSG.YGroups.Y443.Native.Words
import Certificates.Kernel.KDenseP.MonSevenB
import Certificates.Kernel.KDenseP.MonSevenC
public import CFSG.Sporadic.Co2Smith.GlC0MarkInputs
import Certificates.Kernel.Co2Smith.Cox
import Certificates.Data.Kernel.Co2Smith.Mark
import Certificates.Data.Kernel.Co2Smith.Cox
import Certificates.Kernel.Co2Smith.LettersData
import Certificates.Kernel.Co2Smith.CoxData
import Certificates.Kernel.Co2Smith.MarkK
import CFSG.Yardstones.Md0ec50421ce4.Assembly
import CFSG.Yardstones.Md0ec50421ce4.Goals
public import CFSG.CGT.A8S.N0EnumInputs
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Sec5One
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral
public import CFSG.Certificates.Kernel.Census.SiftSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.A6Leaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentSyl
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAlt
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut
public import CFSG.HardMathSupport.Solomon.LocalBalance.ONFacts
public import CFSG.LargeExtraspecial.AS62EnumInputs
public import CFSG.LargeExtraspecial.S10SixE
public import CFSG.LargeExtraspecial.S10SixF
public import CFSG.LargeExtraspecial.S10SixH
public import CFSG.LargeExtraspecial.S10SixI
public import CFSG.LargeExtraspecial.S10SixJ
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118T
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import CFSG.RankThree.PartTwo.KFacts.KP4Aut
public import CFSG.RankThree.PartTwo.KFacts.KP4Gen
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
public import Certificates.Kernel.Sporadic.SuzH.Proof

public section

universe u v w

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.lc_gl_theorem_a
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (m : ℕ) (hm : 4 ≤ m)
    (ha : ∀ q ∈ GLABeta (m + 1) G, GLAWeakCoreLocal G q)
    (hb : ∀ q ∈ GLABeta m G, GLAWeakCoreLocal G q ∨ GLADeltaZero G q)
    (hc : ∃ q ∈ GLABeta m G, GLATwoLocalRank q G = m ∧ GLADeltaZero G q) :
    ∃ p ∈ GLABeta m G, GLATwoLocalRank p G = m ∧ GLADeltaZero G p ∧
      ((p = 3 ∧ GLAGF2Type G) ∨
        ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
          GLASStar p B x L ∧ GLAStandardType p B x L) :=
  CFSG.Yardstones.Md0ec50421ce4.theorem_a_of_yardstones
    CFSG.Yardstones.Md0ec50421ce4.ys01
    CFSG.Yardstones.Md0ec50421ce4.ys02
    CFSG.Yardstones.Md0ec50421ce4.ys03
    CFSG.Yardstones.Md0ec50421ce4.ys04
    CFSG.Yardstones.Md0ec50421ce4.ys05
    CFSG.Yardstones.Md0ec50421ce4.ys06
    CFSG.Yardstones.Md0ec50421ce4.ys07
    CFSG.Yardstones.Md0ec50421ce4.ys08
    CFSG.Yardstones.Md0ec50421ce4.ys09
    CFSG.Yardstones.Md0ec50421ce4.ys10
    CFSG.Yardstones.Md0ec50421ce4.ys11
    G hnonab hK hchar he m hm ha hb hc

end CFSG.Open
