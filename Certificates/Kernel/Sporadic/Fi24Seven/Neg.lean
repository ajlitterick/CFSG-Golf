module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Seven.Data
public import Certificates.Data.Kernel.Spor.SlpPlan

public section

set_option maxRecDepth 400000

namespace CFSG.KD.F24S

open CFSG.KC.SlpM CFSG.KC.Ord

@[expose] noncomputable def ckT (W : List (List Nat)) (R' : Nat → Nat) (ins : List (Nat × Nat))
    (nodes : List Nat) (outs : List (Nat × Nat)) (eqs neqs : List (List Nat × List Nat)) : Bool :=
  chunkOK CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE CFSG.KD.BrFi24.VLD (CFSG.KD.BrFi24.RB (nat_lit 23))
    (CFSG.KD.BrFi24.RB (nat_lit 24)) (R (nat_lit 0)) W R' ins nodes outs eqs neqs


theorem neg_eq : notB (ckT W7 R [] [] [] [([2], [4])] []) = true := by quickRfl


end CFSG.KD.F24S

end
