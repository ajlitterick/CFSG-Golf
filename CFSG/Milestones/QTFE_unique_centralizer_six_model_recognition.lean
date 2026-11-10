module

public import CFSG.Quasithin.QTFE14Cat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsKInputs
import Certificates.Kernel.HSA312.Struct
import Certificates.Kernel.HSQuot.Final
import CFSG.Quasithin.EmptyFaithful.TopAssemblyFrontier24
import CFSG.Yardstones.M51a66d7c6d3f.Goals
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

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem qtfe_unique_centralizer_six_model_recognition
    (G : Type) [Group G] [Finite G] (T Mc : Subgroup G)
    (hQTFE : CFSG.Quasithin.quasithinQTFE14Cat G T Mc) :
    Nonempty (G ≃* NativeSporadic.J2) ∨
    Nonempty (G ≃* NativeSporadic.J3) ∨
    LieModel G .trialityD4 0 2 1 ∨
    LieModel G .Tits 0 2 1 ∨
    (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ∧
      Nonempty (G ≃* ↥⁅adjointGroup .G2 k, adjointGroup .G2 k⁆)) ∨
    Nonempty (G ≃* NativeSporadic.M12) :=
  CFSG.Quasithin.qtfe_unique_centralizer_of_two CFSG.Yardstones.M51a66d7c6d3f.ys02_noNonlinSp4
    CFSG.Yardstones.M51a66d7c6d3f.ys03_noNonlinSpGt4 G T Mc hQTFE

end CFSG.Milestones
