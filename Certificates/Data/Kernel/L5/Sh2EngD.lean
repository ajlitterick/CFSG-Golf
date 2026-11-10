module

public import Certificates.Data.Kernel.L5.EngWit
public import Certificates.Data.Kernel.L5.Sh2Mul
import CFSG.Certificates.Kernel.Common.JsonGzEval
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz_eval CFSG.KD.L5 "Certificates/Data/Kernel/L5/data/sh2eng.json.gz" 4179
  7801186606563420261 (cszP : Nat) (maxSubsP : List Nat) (ciPA : Nat) (ciPB : Nat)
  (tagsA : List (List Nat)) (tagsB : List (List Nat))

#kc_repo #kc_json_gz_eval CFSG.KD.L5.Sh2EngR "Certificates/Data/Kernel/L5/data/sh2eng.json.gz"
  4179 7801186606563420261 (repsA : List Nat) (repsB : List Nat) (xA : Nat) (xB : Nat)
  (mgensR : List Nat) (ctxA : List (List Nat)) (ctxB : List (List Nat))

namespace CFSG.KD.L5

open CFSG.GH74.GLS.C3.Layer2.L5.Fus


end CFSG.KD.L5

end
