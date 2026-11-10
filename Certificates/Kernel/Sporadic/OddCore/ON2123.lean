module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.DecSLSound
public import CFSG.Certificates.Kernel.Spor.PermLSound
public import CFSG.Sporadic.ONOddCore.LocalAutDataCheckInputs
meta import CFSG.Sporadic.ONOddCore.LocalAutDataCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.LocAutT CFSG.Sporadic.ONOddCore.localAutText

namespace CertificateChecks.KernelSpor.ON2123

open CFSG.Sporadic.ONOddCore CFSG.KS.DecSL CFSG.KS.PermL CFSG.ONSchreier.Native

@[expose] noncomputable def localFormK (c : LocalCert) : Bool :=
  c.quotGens.length == 2 && c.quotGens.all (fun a => permLK 120 a.toList) &&
    c.records.map (fun r => (r.diag, r.field, r.graph)) == tripleList &&
    c.records.all (fun r => r.images.length == 2 && r.images.all (fun a => permLK 120 a.toList) &&
      r.lifts.all liftFormOK) &&
    c.records.map (fun r => r.lifts.length) == [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0]


theorem digits : digitsSLOK LocAutT.chars = true := by
  quickRfl

theorem formK : localFormK (decodeCert (natsSL LocAutT.chars)) = true := by
  quickRfl


end CertificateChecks.KernelSpor.ON2123

end
