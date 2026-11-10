module

public import CFSG.RankThree.PartTwo.Toolkit.BloomMonoStdInputs
import Certificates.Kernel.Misc.Perm.BloomMono

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Toolkit
  CFSG.RankThree.PartTwo.Toolkit.Raw Subgroup CFSG.RankThree.SubgroupLists in
open scoped Matrix in
theorem certificate8172 : monoCheck = true := KernelMisc.BloomMono.facts

end Certificates
