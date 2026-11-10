
module

public import Certificates.Certificate7019Base
meta import CFSG.Sporadic.Schreier.J4SOrbitsBase

import Certificates.Kernel.J4Count.Fuse
meta import CFSG.Sporadic.Schreier.J4SNoCompData
meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SOrderBase
import CFSG.Quasithin.H13.J4Classes
import Certificates.Kernel.J4Count.FuseBase1

public section

namespace Certificates

open CertificateChecks

theorem certificate7019 :
    Nat.card {w : CFSG.Sporadic.J4.Row //
      w ∈ MulAction.orbit CFSG.Sporadic.J4.J CFSG.Sporadic.J4Schreier.v ∧
        CFSG.Quasithin.H13.J4.tJ • w = w} = 52349 := KernelJ4Count.Fuse.card_fix_tJ'

end Certificates
