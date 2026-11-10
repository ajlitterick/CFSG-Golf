module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs
import Certificates.Kernel.PresLetters.F7771
import Certificates.Kernel.PresLetters.F7771A
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.LieType.BorelTits.CompleteFlag
public import Certificates.Data.Kernel.Bounds.TableFact

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters7771

#kc_forall_chunks idx (fun k => KB.TableFact 4
  ((burnsideF48t_u52Ws (burnsideF48t_u52Cands.getD k (0, 0, 0, 0)).1
    (burnsideF48t_u52Cands.getD k (0, 0, 0, 0)).2.1
    (burnsideF48t_u52Cands.getD k (0, 0, 0, 0)).2.2.1).map encW)
  ((subsetOf 4 [0, 1, 2]).map fun x => [(x.val, true)])
  (burnsideF48t_u52Cands.getD k (0, 0, 0, 0)).2.2.2) 24 CFSG.KBFact.F7771a 1


end CertificateChecks.PresLetters7771

namespace Certificates


end Certificates
