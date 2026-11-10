module

public import CFSG.Yardstones.M19b85589cdfc.Goals
public import CFSG.Yardstones.M19b85589cdfc.Reduction
public import CFSG.Milestones.LC_GL_embedding_theorem_D1_rank_four
import Certificates.Kernel.Misc.E6StdSlp
import Certificates.Kernel.KDense.Y443
public import CFSG.GH74.E2.OuterCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenModule
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.Setup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsTitsPair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDelOrigData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelH0
public import CFSG.Quasithin.Background.G2Omega4PlusQuot
public import CFSG.Quasithin.EmptyFaithful.S153E58In
public import CFSG.Quasithin.EmptyFaithful.S153EB6C
public import CFSG.Quasithin.H13.A5RawNat
public import CFSG.Quasithin.H13.A5S1328Blk2
public import CFSG.Quasithin.H13.A5S1328Blk3
public import CFSG.Quasithin.H13.A5S1328Sym2
public import CFSG.Quasithin.H13.A5S1328Sym5
public import CFSG.Quasithin.H13.A5S1328Vertex
public import CFSG.Quasithin.H13.L1332
public import CFSG.Quasithin.H13.VolIC113c1
public import CFSG.Quasithin.Vol2.Ch10SecAFactsOrth
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym4
public import CFSG.Quasithin.Vol2.Ch11SecSSym5
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27C
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27E
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.RankThree.PartOne.N143.QEqual
public import CFSG.RankThree.PartTwo.Sec19.Step1914E

public section

namespace CFSG.Yardstones.M19b85589cdfc

theorem lc_gl_embedding_theorem_d2_rank_four_of_goals
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Open.IsKProper G) (hchar : CFSG.Open.IsCharTwoType G)
    (he : 4 ≤ CFSG.Open.evenRank G)
    (hδ₁ : CFSG.Open.GLBDeltaOne G) (hδ₂ : CFSG.Open.GLBDeltaTwo G)
    (p : ℕ) (hp : p ∈ CFSG.Open.GLBBetaFour G) (P : Sylow p G)
    (M : Subgroup G) (hM : CFSG.Open.GLBIsMaxTwoLocal M)
    (hPM : CFSG.Open.GLBCore p 2 (P : Subgroup G) ≤ M)
    (Q : Subgroup G) (hQ : IsPGroup p Q) (hQrank : CFSG.Open.pRank p Q = 2)
    (hQM : CFSG.Open.GLBCore p 1 Q ≤ M)
    (H : Subgroup G) (hH : CFSG.Open.IsTwoLocal H) (hQH : Q ≤ H) :
    H ≤ M :=
  lc_gl_embedding_theorem_d2_rank_four_of_yardstones
    CFSG.Milestones.lc_gl_embedding_theorem_d1_rank_four
    CFSG.Milestones.cl_lit_classical_involution_theorem_models
    ys01_subfieldPairOmegaPlusF2
    ys02_subfieldPairOmegaMinusF2
    ys03_seitzExcAnisotropicNotG2ThreePlus
    ys04_seitzExcOuterCycResiduals
    ys05_gls3PlusReeG2
    ys06_kFactChevGraphOrbit
    ys07_agl81I516SymOver
    ys08_twistedE6TypeBound
    ys09_orthMinusCentOb
    ys10_e0NonShortNotCaseIStatement
    ys11_quaternionInspectionLie
    G hnonab hK hchar he hδ₁ hδ₂ p hp P M hM hPM Q hQ hQrank hQM H hH hQH

end CFSG.Yardstones.M19b85589cdfc
