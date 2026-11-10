module

public import CFSG.Sporadic.HNSchreier.ArchCheckInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
import Certificates.Support.HN2095TreeDecide
meta import Certificates.Support.HN2095TreeDecide
import all Init.Data.String.Defs
import all Init.Data.Nat.Fold
meta import CFSG.Sporadic.HNSchreier.ArchCheckInputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option cfsg.hn2095.masked true

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native

namespace CertificateChecks.Batch2095

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native


end CertificateChecks.Batch2095

namespace Certificates

open CertificateChecks


end Certificates
