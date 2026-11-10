module

public meta import CFSG.Sporadic.ONOddCore.LocalAutPayload
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public import Certificates.Certificate2123

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier.Native

theorem local_form_cert : localFormOK localCert = true :=
  Certificates.certificate2123

end CFSG.Sporadic.ONOddCore
