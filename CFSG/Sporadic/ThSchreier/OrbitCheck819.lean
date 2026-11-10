
module


public import CFSG.Sporadic.ThSchreier.Transporter
public import CFSG.Sporadic.ThSchreier.LocalOrbit
public meta import CFSG.Sporadic.ThSchreier.Transporter
public meta import CFSG.Sporadic.ThSchreier.LocalOrbit
public import Certificates.Certificate2315

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

theorem isRows_rowsT : IsRows rowsT involT :=
  (isRows_rowsVInv.mul isRows_a).mul isRows_rowsV

termination_by i
decreasing_by exact _h.2

theorem orbit_facts : orbitChecks orbTable = true :=
  Certificates.certificate2315

end CFSG.Sporadic.ThSchreier
