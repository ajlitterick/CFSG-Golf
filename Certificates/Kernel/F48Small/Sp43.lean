module

public import CFSG.Milestones.ASVolI.F48.Small.Sp43Inputs
public import Certificates.Data.Kernel.F48Small.Pack
public import Certificates.Kernel.SporSch.Th.GenStr
public import Certificates.Data.Kernel.DcK

public section

#kss_strof CertificateChecks.KernelF48S.Sp43P1 CFSG.ASVolI.burnsideF48s_sp43P1Str

set_option maxRecDepth 100000 in
#kss_strof CertificateChecks.KernelF48S.Sp43P2 CFSG.ASVolI.burnsideF48s_sp43P2Str

namespace CertificateChecks.KernelF48S

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L


end CertificateChecks.KernelF48S
