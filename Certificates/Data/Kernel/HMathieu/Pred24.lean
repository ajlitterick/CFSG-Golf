
module

public import Certificates.Data.Kernel.HMathieu.PredHF
public import Certificates.Data.Kernel.HMathieu.Tab
public import Certificates.Data.Kernel.HMathieu.Avoid
public import CFSG.Quasithin.AppendixH.H14.H141C1Inputs
public import CFSG.Quasithin.AppendixH.H16.H165Inputs

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.AppendixH.H14

@[expose] def xiCandsK (Mc : List (List Nat)) (m : Nat) (S : List Nat) : List Nat :=
  (S.filter (· != m)).flatMap fun s => fixMasks 11 actM [Mc.getD s []]

@[expose] def pred24K (Mc : List (List Nat)) (L S : List Nat) (st : List (List Nat) × List Nat) :
    Bool :=
  let k := L.length
  let F := st.2
  let d := Nat.log 2 F.length
  decide (k ≤ 6) && (k == 0 || !decide (11 - d ≤ k + 1) || avoidK 11 3 o2Masks24 F) &&
    (k != 1 || decide (4 ≤ 11 - d)) &&
    (k != 6 || indepCheck 11 (xiCandsK Mc 191 S) (pickBasis (xiCandsK Mc 191 S)) || d == 3)


@[expose] def maskOf (n : Nat) (f : Nat → Bool) : Nat :=
  (List.range n).foldr (fun k acc => if f k then acc ||| 1 <<< k else acc) 0


end CFSG.KC.HMathieu

end
