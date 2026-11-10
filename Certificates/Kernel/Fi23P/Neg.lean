module

public import Certificates.Kernel.Fi23P.Small
public import Certificates.Data.Kernel.Fi23R.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23P

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23P CFSG.KD.Fi23K

set_option Elab.async false


@[expose] noncomputable def lab1 (x : Nat) : Nat := Nat.add (labP x) (nat_lit 1)


end CFSG.KD.Fi23P

end
