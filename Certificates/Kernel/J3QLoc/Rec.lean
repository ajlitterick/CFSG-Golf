module

public import Certificates.Kernel.J3Ref.RecC
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.LocalQT.PEnumD
public import CFSG.Certificates.Kernel.Common.Each
public import Certificates.Data.Kernel.Spor.PEnumB
public import Certificates.Data.Kernel.Spor.MulHQ
meta import Certificates.Data.J3Cls
public meta import CFSG.Sporadic.SmallOddCore.J3LocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ3QLoc

open CFSG.SectionRank.QTK.Insp443.J3Cls CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CertificateChecks.KernelJ3Ref

meta def qGM : Array (Array Nat) := j3QGens.toArray.map natArr

meta def qIM : Array (Array Nat) := qGM.map invM

meta def qRecM : Array (Array Nat) := recOfM qGM

meta def qHVM : Array (Array Nat) := hvOfM qRecM

meta def qClM : Array Nat := clOfM qRecM qGM

meta def qNpM : Array Nat := Id.run do
  let idx := indexM qRecM
  let mut out : Array Nat := #[]
  for x in qRecM do
    for c in cGM do
      out := out.push (idx.getD (compM (compM c x) (invM c)) qRecM.size)
  return out

end CertificateChecks.KernelJ3QLoc

#kmulh CertificateChecks.KernelJ3QLoc.J3RQ 6156 13 CertificateChecks.KernelJ3Ref.ids5M
  CertificateChecks.KernelJ3QLoc.qGM CertificateChecks.KernelJ3Ref.idM 100

#kmisc_packarrs CertificateChecks.KernelJ3QLoc.J3QI CertificateChecks.KernelJ3QLoc.qIM 13

#kmisc_packarrs CertificateChecks.KernelJ3QLoc.J3RQV CertificateChecks.KernelJ3QLoc.qHVM 64

#krows32 CertificateChecks.KernelJ3QLoc.J3RQCl CertificateChecks.KernelJ3QLoc.qClM

#krows32 CertificateChecks.KernelJ3QLoc.J3RQNp CertificateChecks.KernelJ3QLoc.qNpM

namespace CertificateChecks.KernelJ3QLoc

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.PEnumB
open CertificateChecks.KernelSpor CertificateChecks.KernelJ3Ref


@[expose] noncomputable def q_hv (b : Nat) : Bool :=
  allBlk (Nat.mul b 8) (hvK 6156 13 (mask 13) J3RQ.T J3RQV) 8

#kc_each CertificateChecks.KernelJ3QLoc.q_hv 0 4


end CertificateChecks.KernelJ3QLoc

end
