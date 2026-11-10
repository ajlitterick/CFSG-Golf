module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriFix
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenG2Two
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofGammaInner
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4OuterAux.Two
import CFSG.Certificates.LiftedSchreierData
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2TwoHolds
import CFSG.Monster.AxisCount.HSIdentBaby
import CFSG.Monster.AxisCount.HSIdentRec0
import CFSG.Monster.AxisCount.HSIdentRec1
import CFSG.Monster.AxisCount.HSIdentRec2
import CFSG.Monster.AxisCount.HSIdentRec3
import CFSG.Monster.AxisCount.HSIdentRec4
import CFSG.Monster.AxisCount.HSIdentRec5
import CFSG.Monster.AxisCount.HSIdentRec6
import CFSG.Monster.AxisCount.HSIdentRec7
import CFSG.Monster.AxisCount.HSIdentSmall
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.RankThree.PartTwo.Sec13.Item135
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item143N
import CFSG.RankThree.PartTwo.Sec15.Item157
import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofFus
import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item167Proof
import CFSG.RankThree.PartTwo.Sec16.Item16Tail17
import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
import CFSG.RankThree.PartTwo.Sec17.Item1724Two
import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
import CFSG.RankThree.PartTwo.Sec17.RouteProvers
import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec21.Item226Steps
import CFSG.RankThree.PartTwo.Sec21.Item229
import CFSG.RankThree.PartTwo.Toolkit.M12Local
import CFSG.RankThree.S4Free.SuzukiEight
import CFSG.Sporadic.Bridge.Catalogue
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartTwo CFSG.PGLModel CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

section TriFixCard


theorem card_fix_le_triFix {K₃ : Type} [Field K₃] [Finite K₃]
    (hK₃ : Nat.card K₃ = (2 ^ 1) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (2 ^ 1))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    Nat.card ↥(fixSubgroup φ) ≤ 12096 := by
  rcases Y10GTri.triFixModel (le_refl 1) hK₃ Fr hFr φ hφ3 hφ with
    ⟨F₀, hF₀field, hF₀fin, hF₀card, ⟨e⟩⟩ | ⟨F, hFfield, π, hF, ⟨e⟩⟩
  · letI := hF₀field
    letI := hF₀fin
    calc Nat.card ↥(fixSubgroup φ) = Nat.card ↥(adjointGroup Tag.G2 F₀) :=
          Nat.card_congr e.toEquiv
      _ = 12096 :=
          CFSG.ComponentClassification.ExcSelector.card_adjointGroup_G2_two
            (by simpa using hF₀card)
      _ ≤ 12096 := le_rfl
  · letI := hFfield
    letI := hF.finite
    calc Nat.card ↥(fixSubgroup φ) =
          Nat.card ↥(CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ 1) F)) :=
          Nat.card_congr e.toEquiv
      _ = (2 ^ 1) ^ 3 * ((2 ^ 1) ^ 2 - 1) *
            cond π ((2 ^ 1) ^ 3 - 1) ((2 ^ 1) ^ 3 + 1) :=
          CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.card_projImage_glPi_three hF
      _ ≤ 12096 := by cases π <;> norm_num [cond]

end TriFixCard

end CFSG.LocalAnalysis.GLTheoremA.K144
