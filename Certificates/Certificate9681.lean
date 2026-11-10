module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12CoverData
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12CoverData
public meta import CFSG.Sporadic.Schreier.M12Data
public meta import CFSG.Sporadic.Schreier.CountSpec
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Count
import Certificates.Kernel.SporSch.M12Cover9681G
public meta import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.Sporadic.Schreier.M12Data
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Hyp
import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermCands
import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermSix
import CFSG.Quasithin.Vol2.Ch4Sec1Lem415
import CFSG.Quasithin.Vol2.Ch4Sec4Lem445
import CFSG.Quasithin.Vol2.KGFactC31A7
import CFSG.Quasithin.Vol2.KGFactC31Ident
import CFSG.Quasithin.Vol2.KGFactC31Rad
import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1

public section

namespace Certificates

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native in
open CFSG.AGLEmbedding.KFactProofs.M12Cover in
theorem certificate9681 : countProducts 12 m12CoverBad (levelTables m12Certificate) (idT 12) = 0 :=
  CertificateChecks.KernelSporSch.M12Cover9681.cover_ok

end Certificates
