module

public import Certificates.Data.Kernel.Fi22.Cent
public import Certificates.Data.Kernel.Spor.Row
public import Certificates.Kernel.Sporadic.RowsWCmd
public meta import CFSG.Sporadic.Fi22.TriangularCfgInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Cfg

open CFSG.Sporadic.Th.Native

meta def cfgTabs : Array Nat := Id.run do
  let O := CFSG.Sporadic.Fi22.Native.orbitData ()
  let mut out : Array Nat := #[]
  for i in [0:8] do
    let T := CFSG.Sporadic.Fi22.Native.rank3CfgTab O i
    for x in [0:3510] do
      out := out.push (ap T x)
  return out

end CertificateChecks.KernelFi22Cfg

#krowsw CertificateChecks.KernelFi22Cfg.CT 12 CertificateChecks.KernelFi22Cfg.cfgTabs

namespace CertificateChecks.KernelFi22Cfg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Row CFSG.KS.Fi22Cent


end CertificateChecks.KernelFi22Cfg

end
