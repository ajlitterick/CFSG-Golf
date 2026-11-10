module

public import Certificates.Data.Kernel.U52.PtLn
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Kernel.U52.ChainX
public import Certificates.Kernel.Misc.Perm.CharsCat
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs3
public meta import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs3
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars_cat CFSG.KC.U52PL.PtsT CFSG.ASVolI.burnsideF48t_u52PtStr
#kmisc_hexflat CFSG.KC.U52PL.PtsT CFSG.ASVolI.burnsideF48t_u52PtStr 1 5 2 165
#kmisc_packarrs CFSG.KC.U52PL.LP CFSG.ASVolI.burnsideF48t_u52LnPts 8
#kmisc_packarrs CFSG.KC.U52PL.UP CFSG.ASVolI.burnsideF48t_u52U 2

namespace CFSG.KC.U52PL

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum CertificateChecks.KernelU52


end CFSG.KC.U52PL

end
