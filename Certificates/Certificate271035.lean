module

public import Certificates.Data.F4NA
import Certificates.Kernel.F4NA.Glue

public section

open CFSG.RankThree.PartOne.F106

namespace Certificates

open CFSG.RankThree.PartOne.F106 in
theorem certificate271035 : F4NACheck :=
  CFSG.KD.F4NA.naCheck_true (F4SylowCert.facts_of_check f4ThreeCert
    Certificates.certificate271060)

end Certificates
