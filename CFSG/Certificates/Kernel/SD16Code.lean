module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.GH74.E2.Alpha1AutCertInputs

public section

namespace CFSG.KS.SD16Code

open CFSG.KC.Loop CFSG.GH74.E2 CFSG.Semidihedral

local instance instDecEqSD16MForCode : DecidableEq SD16M := inferInstance

end CFSG.KS.SD16Code

end
