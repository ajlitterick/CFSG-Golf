module

public import CFSG.Milestones.ASVolI.F48.Small.Sp43eInputs
public import Certificates.Data.Kernel.F48Small.Pack
public import Certificates.Kernel.SporSch.Th.GenStr
public import Certificates.Data.Kernel.DcK

public section

#kss_strof CertificateChecks.KernelF48S.Sp43eP1 CFSG.ASVolI.burnsideF48s_sp43eP1Str

set_option maxRecDepth 100000 in
#kss_strof CertificateChecks.KernelF48S.Sp43eP2 CFSG.ASVolI.burnsideF48s_sp43eP2Str

namespace CertificateChecks.KernelF48S

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L


end CertificateChecks.KernelF48S
