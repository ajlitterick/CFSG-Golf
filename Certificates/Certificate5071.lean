
module

public import Certificates.Certificate5071Base
import all Certificates.Certificate5071Base

import CFSG.Certificates.Kernel.L5.HFVSound

public section

open Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5
  CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5H

namespace CertificateChecks.Batch5071

open Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5
  CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5H

set_option maxRecDepth 100000

private theorem planes0_fam0_32 : ∀ V ∈ planes0, V.toFinset ∈ fam0 := planes0_fam0

private theorem fam0_planes0_33 : ∀ F ∈ fam0, ∃ W ∈ planes0, W.toFinset = F := fam0_planes0

private theorem planes1_fam1_34 : ∀ V ∈ planes1, V.toFinset ∈ fam1 := planes1_fam1

private theorem fam1_planes1_35 : ∀ F ∈ fam1, ∃ W ∈ planes1, W.toFinset = F := fam1_planes1

end CertificateChecks.Batch5071

namespace Certificates


end Certificates
