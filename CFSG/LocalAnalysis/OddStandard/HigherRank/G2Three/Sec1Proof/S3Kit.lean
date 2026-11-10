module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabPc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabDecode
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Words3
import Certificates.Kernel.G2Three.Sec1T3Glue
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.S11
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabPred4
public import Std.Data.HashSet
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabPred2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.FrameLe
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabRank
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ModelL
public import Certificates.Certificate442054
public import CFSG.Certificates.CosetTablePresented
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsL
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabHom
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Words

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

theorem s3_facts
    (m : G23Model G) :
    (frameOf m).Fact11 m.L ∧ (frameOf m).Fact12 ∧ (frameOf m).Fact13 ∧ (frameOf m).Fact14 ∧
      (frameOf m).Fact15 :=
  Certificates.certificate442054 m

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
