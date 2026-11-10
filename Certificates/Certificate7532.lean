module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.Milestones.ASVolI.F48.Small.G2dInputs
import Certificates.Kernel.PresLetters.F7532
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Data.Kernel.Bounds.TableFact

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters7532

#kc_forall_chunks idx (fun j => KB.TableFact 5 ((burnsideF48s_g2dWs j).map encW)
  ((subsetOf 5 [0, 1, 2, 4]).map fun x => [(x.val, true)]) (if j % 2 = 1 then 63 else 1))
  4 CFSG.KBFact.F7532a 1

#kc_forall_chunks res (fun j => KB.TableFact (subsetOf 5 [0, 1, 2, 4]).length
  ((burnsideF48s_g2dWsB j).map encW) [] 96) 4 CFSG.KBFact.F7532b 1

end CertificateChecks.PresLetters7532

namespace Certificates


end Certificates
