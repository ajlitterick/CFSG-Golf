module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG
import Certificates.Kernel.PresLetters.F7777
import Certificates.Kernel.PresLetters.F7771A
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.LieType.BorelTits.CompleteFlag
public import Certificates.Data.Kernel.Bounds.TableFact

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters7777

#kc_forall_chunks idx (fun k => KB.TableFact 5
  ((burnsideF48t_u52eWs (burnsideF48t_u52eCands.getD k (0, 0, 0, 0)).1
    (burnsideF48t_u52eCands.getD k (0, 0, 0, 0)).2.1
    (burnsideF48t_u52eCands.getD k (0, 0, 0, 0)).2.2.1).map encW)
  ((subsetOf 5 [0, 1, 2, 4]).map fun x => [(x.val, true)])
  (burnsideF48t_u52eCands.getD k (0, 0, 0, 0)).2.2.2) 30 CFSG.KBFact.F7777a 1


end CertificateChecks.PresLetters7777

namespace Certificates


end Certificates
