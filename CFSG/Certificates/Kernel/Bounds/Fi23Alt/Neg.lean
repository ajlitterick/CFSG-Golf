module

public import CFSG.Certificates.Kernel.Bounds.Fi23Alt.Route
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.Fi23Alt.Neg

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec true false b


end CFSG.KBRoute.Fi23Alt.Neg

end
