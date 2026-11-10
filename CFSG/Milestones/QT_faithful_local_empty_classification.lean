module

public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsKInputs
import Certificates.Kernel.HSA312.Struct
import Certificates.Kernel.HSQuot.Final
import CFSG.Quasithin.EmptyFaithful.TopAssemblyFrontier24
import CFSG.Yardstones.M71b2fd3d34b9.Goals
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListMain
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CoverEven
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CoverOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TChain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TUniq
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuterCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs3
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B3Facts
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.JonesParshallCurtisWeyl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvGenE
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvMaxBase
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.Quasithin.Recognition.M12AmalAutClass
public import CFSG.Quasithin.Recognition.M12AmalInst
public import CFSG.Quasithin.Recognition.M12AscFive
public import CFSG.Quasithin.Recognition.M12AscY3
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Sporadic.HeldB.ClassCount
public import CFSG.Sporadic.J4.QT2LocCntProof
public import CFSG.Sporadic.Presentation.M24Exact
public import CFSG.Sporadic.Schreier.RuLOdd
public import CFSG.Sporadic.Schreier.RuZClass
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Timmesfeld.Moufang.A6
public import CFSG.Timmesfeld.Moufang.Cases
public import CFSG.Timmesfeld.Moufang.J2Check
public import CFSG.Timmesfeld.Moufang.J2MatCheck
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.Special.TwoCore
import CFSG.Quasithin.Background.C116Three.L3Local
import CFSG.Quasithin.Background.C116Two.FixMod
import CFSG.Quasithin.Background.C116Two.NatLin2Linear
import CFSG.Quasithin.H13.GoldschmidtC137SQMain
import CFSG.Quasithin.MS93.Burnside.Mag568Main
import CFSG.Quasithin.MS93.MRes45

public section

namespace CFSG.Milestones

open CFSG.Assembly CFSG.Assembly.Quasithin

theorem qt_faithful_local_empty_classification
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : QuasithinUnique.quasithinIsQTKECat G)
    (T : Sylow 2 G)
    (hMT : ∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧
      quasithinIsMaxTwoLocal M₁ ∧ quasithinIsMaxTwoLocal M₂ ∧
      (T : Subgroup G) ≤ M₁ ∧ (T : Subgroup G) ≤ M₂)
    (hLf : ∀ L : Subgroup G, ¬ quasithinIsFaithfulLocal (T : Subgroup G) L) :
    Blueprint.Catalog G :=
  CFSG.Quasithin.qt_faithful_local_empty_of_two CFSG.Yardstones.M71b2fd3d34b9.ys01_noNonlinSp4
    CFSG.Yardstones.M71b2fd3d34b9.ys02_noNonlinSpGt4 G hnonab hqtke T hMT hLf

end CFSG.Milestones
