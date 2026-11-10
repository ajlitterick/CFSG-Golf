
module

meta import CFSG.Sporadic.Schreier.J4SOrbitsBase

public import CFSG.Sporadic.J4.QT2LocX0MainBase
import Certificates.Kernel.J4Count.Fix5
meta import CFSG.Sporadic.Schreier.J4SNoCompData
meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.J4.QT2AGen
public import CFSG.Sporadic.J4.QT2LocZProof
public import CFSG.Sporadic.J4.QTOutChar
public import CFSG.Sporadic.J4Base
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BAction
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BCasesBase
import CFSG.Quasithin.Background.A3Structure36BFrattini
import CFSG.Quasithin.Background.A3Structure36BHeisBase
import CFSG.Quasithin.Background.A3Structure36BHomocyclic
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.A3Structure36BStarBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure37Base
import CFSG.Quasithin.Background.A3Structure37Comm
import CFSG.Quasithin.Background.A3Structure37Frattini
import CFSG.Quasithin.Background.A3Structure37KeyBase
import CFSG.Quasithin.Background.A3Structure37Schur
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B1MoreElevenE
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.Vol2.Ch1Local
import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
import Certificates.Kernel.J4Count.Cent11Base
import Certificates.Kernel.J4Count.FixC
import Certificates.Kernel.J4Count.FixCPairBase1

public section

namespace Certificates

open CertificateChecks

theorem certificate4009 :
    Subgroup.centralizer ({CFSG.Sporadic.J4.QT2.fiveElt} : Set CFSG.Sporadic.J4.J) =
      CFSG.Sporadic.J4.QT2.X0Sub := KernelJ4Count.Five.centralizer_fiveElt_eq'

end Certificates
