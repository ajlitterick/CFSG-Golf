module

public import CFSG.Milestones.ASVolI.F48.Small.Sp42Inputs
import Certificates.Kernel.PresLetters.F7530
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Data.Kernel.Bounds.TableFact

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters7530

#kc_forall_chunks idx (fun j => KB.TableFact 5 ((burnsideF48s_sp42Ws j).map encW)
  ((subsetOf 5 [0, 1, 2, 3]).map fun x => [(x.val, true)]) (if j = 1 then 15 else 1))
  4 CFSG.KBFact.F7530a 1

#kc_forall_chunks res (fun j => KB.TableFact (subsetOf 5 [0, 1, 2, 3]).length
  ((burnsideF48s_sp42WsA j).map encW) [] 48) 4 CFSG.KBFact.F7530b 1

end CertificateChecks.PresLetters7530

namespace Certificates


end Certificates
