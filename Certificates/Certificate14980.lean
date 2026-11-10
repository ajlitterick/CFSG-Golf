
module

public import Certificates.Certificate14980Base
import all Certificates.Certificate14980Base

public meta import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.NatCheckInputs
import CFSG.RankThree.PartOne.S11c.HNSevenFixBase
meta import CFSG.Sporadic.HNSchreier.OrbitCheck
meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
meta import CFSG.Sporadic.HNSchreier.PrimCheck
meta import CFSG.Sporadic.HNSchreier.LocalData
meta import CFSG.Sporadic.HNSchreier.MaskCheck
meta import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
open CFSG.RankThree.PartOne.HNRed.Native in
theorem certificate14980 : (sevenChecksO (hnsData.orbit ()) = true) ∧ (sevenNatCheck = true) :=
  ⟨CertificateChecks.Batch14980.seven_ok, CertificateChecks.Batch14980.nat_ok⟩

end Certificates
