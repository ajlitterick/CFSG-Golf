module

public import Certificates.Kernel.Census.M22II.Data
import all Certificates.Kernel.Census.M22II.Data
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.M22II

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kS : penumOK 24 5 m22IISG [0, 1, 2, 3, 4, 5, 8, 9] m22IICS = true := by quickRfl

theorem kR : ((List.range m22IICS.pts.size).all fun p =>
    prootOK 24 5 m22IINodes (pcN 24 5 m22IINodes) m22IICS.pts[p]! m22IIRoots[p]!) = true := by
  quickRfl

theorem kNs : Nat.beq m22IINodes.size 595 = true := by quickRfl

theorem kXs : Nat.beq m22IIXS.size 1046 = true := by quickRfl

theorem kSz : Nat.beq m22IICS.pts.size 256 = true := by quickRfl

theorem kWt : (List.range' 960 86).all wordF = true := by quickRfl

end CertificateChecks.KernelCensus.M22II

end
