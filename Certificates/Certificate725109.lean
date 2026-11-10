module

public import Certificates.Data.L52Insp443
import Certificates.Kernel.L52Insp443.Final
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

open CFSG.SectionRank.QTK.Insp443.L52

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.QTK.Insp443.L52 in
theorem certificate725109 : chkP52 () = true := KernelL52I.chkP52_true

end Certificates

end
