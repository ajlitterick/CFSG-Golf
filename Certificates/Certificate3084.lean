
module

public import Certificates.Certificate3084Base
meta import CFSG.Sporadic.Schreier.J4SOrbitsBase

import Certificates.Kernel.J4Count.Prim
meta import CFSG.Sporadic.Schreier.J4SNoCompData
meta import CFSG.Sporadic.Schreier.J4SOrbits
import Certificates.Certificate4008

public section

namespace Certificates

open CertificateChecks

theorem certificate3084 : CFSG.Sporadic.J4.J4Facts :=
    { mat := KernelJ4Q.matFacts
      cardHj := KernelJ4Count.card_Hj'
      cardJ := KernelJ4Hub.card_J'
      stab := fun x hx => by
        rw [← KernelJ4Count.stabilizer_v_eq_Hj', MulAction.mem_stabilizer_iff,
          KernelJ4Count.v_eq_root]
        exact hx
      coatom := KernelJ4Count.Prim.isCoatom_Hj'
      simple := KernelJ4Count.Prim.isSimpleGroup_J'
      cosets := Certificates.certificate4008.1
      sizes := Certificates.certificate4008.2 }

end Certificates
