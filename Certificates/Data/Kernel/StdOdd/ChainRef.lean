module

public import Certificates.Data.Kernel.StdOdd.Chain

public section

namespace CFSG.KC.StdOdd.Chain

open CFSG.KC.StdOdd.Orbit


@[expose] noncomputable def pickL (O e : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun i _ ih => List.cons (nthN O i) ih) e

@[expose] noncomputable def dropLast (O : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun x t ih => List.rec (motive := fun _ => List Nat) List.nil (fun _ _ _ => List.cons x ih) t) O

@[expose] noncomputable def tailL (O : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun _ t _ => t) O

@[expose] noncomputable def levSteps (N : Nat) (rs nl : List Nat) (m : Nat) : List (List (List Nat)) :=
  Nat.rec (motive := fun _ => Nat → Nat → List (List (List Nat))) (fun _ _ => List.nil)
    (fun _ ih j N => List.cons (stepsPl N 1 1 (nthN rs j) (nthN nl j))
      (ih (Nat.succ j) (Nat.shiftRight N (Nat.mul 8 (Nat.mul (nthN rs j) (nthN nl j)))))) m 0 N


end CFSG.KC.StdOdd.Chain

end
