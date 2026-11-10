module

public import Certificates.Kernel.Sporadic.RawTreeGen
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.E2065T
public meta import CFSG.Sporadic.FischerOddCore.Fi22QCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22QK

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore

meta def wordA (Q : Array (Array Nat)) (w : List Int) : Array Nat :=
  w.foldr (fun z acc => compA 3510 Q[z.toNat - 1]! acc) (idA 3510)

meta def DTm : List (List Int) := [[5, 3], [6, 4]]

meta def DZm : List (List Int) :=
  [[4, 2, 1, 1], [5, 7, 6, 8], [8, 3, 9, 2, 1], [7, 8, 6, 3, 1], [7, 4, 9, 6, 1, 1]]

meta def ST : Array (Array Nat) := fi22QTwoArr ++ (DTm.map (wordA fi22QTwoArr)).toArray

meta def SZ : Array (Array Nat) := fi22QZeroArr ++ (DZm.map (wordA fi22QZeroArr)).toArray

meta def B : Array Nat := #[0, 1, 2, 3, 6, 4]

@[expose] def DT : List (List Int) := [[5, 3], [6, 4]]

@[expose] def DZ : List (List Int) :=
  [[4, 2, 1, 1], [5, 7, 6, 8], [8, 3, 9, 2, 1], [7, 8, 6, 3, 1], [7, 4, 9, 6, 1, 1]]

end CertificateChecks.KernelSpor.Fi22QK

#ks_rawtree CertificateChecks.KernelSpor.Fi22Q2T 3510 12 64 64 0 CertificateChecks.KernelSpor.Fi22QK.ST
  CertificateChecks.KernelSpor.Fi22QK.B 6 CertificateChecks.KernelSpor.Fi22QK.DT

#ks_rawtree CertificateChecks.KernelSpor.Fi22Q0T 3510 12 64 64 0 CertificateChecks.KernelSpor.Fi22QK.SZ
  CertificateChecks.KernelSpor.Fi22QK.B 9 CertificateChecks.KernelSpor.Fi22QK.DZ

namespace CertificateChecks.KernelSpor.Fi22QK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw


end CertificateChecks.KernelSpor.Fi22QK

end
