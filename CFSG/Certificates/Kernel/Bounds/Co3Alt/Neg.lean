module

public import CFSG.Certificates.Kernel.Bounds.Co3Alt.Route
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.Co3Alt.Neg

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec true false b


end CFSG.KBRoute.Co3Alt.Neg

end
