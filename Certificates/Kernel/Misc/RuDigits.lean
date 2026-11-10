module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Quasithin.Recognition.ModelBridgesJ3Inputs
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.Blueprint.NativeSporadic
meta import CFSG.Open.QuasithinDefs

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelRu.S1 CFSG.Blueprint.NativeSporadic.RuSeed1
#ks_chars CertificateChecks.KernelRu.S2 CFSG.Blueprint.NativeSporadic.RuSeed2
#ks_chars CertificateChecks.KernelRu.D1 CFSG.Open.quasithinRuData1
#ks_chars CertificateChecks.KernelRu.D2 CFSG.Open.quasithinRuData2

namespace CertificateChecks.KernelRu

open CFSG.Quasithin CFSG.Open CFSG.Blueprint.NativeSporadic


end CertificateChecks.KernelRu

end
