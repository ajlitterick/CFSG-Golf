module

public import CFSG.Quasithin.Vol2.KGFactC31RuCoverNative
import Certificates.Kernel.Misc.RuCover.Final
meta import CFSG.Sporadic.Schreier.RuCheckSylow
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.SeededRelations
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Sporadic.Presentation.Common

public section

namespace Certificates

open CertificateChecks

theorem certificate7257 : CFSG.Quasithin.KGC31.RuCover.coverChk () = true := KernelMisc.RuCover.coverChk_true

end Certificates

end
