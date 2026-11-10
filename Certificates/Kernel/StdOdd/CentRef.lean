module

public import Certificates.Kernel.StdOdd.CentAssemble

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KS.StdOdd.Orbit CFSG.KS.StdOdd.Chain
  CFSG.KD.StdOdd.Orbit CFSG.KC.Misc.E6Std CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.Existence.StdOdd.Cert Matrix CFSG.KC.LQT.P

@[expose] def segsL : ℕ → List ℕ → List (List ℕ)
  | 0, _ => []
  | _, [] => []
  | f + 1, n :: t => t.take n :: segsL f (t.drop n)

namespace CentData

variable (D : CentData)


@[expose] noncomputable def covF (sidx : ℕ → ℕ) (R : ℕ) : Bool :=
  allN (lenN D.reps) fun r =>
    (!(Nat.beq (nthN D.st r) 1)) || (List.range R).any fun ri => Nat.beq (sidx ri) r

end CentData


end CFSG.KD.StdOdd.Cent

end
