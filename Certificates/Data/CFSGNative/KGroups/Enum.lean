module

public import Certificates.Data.CFSGNative.KGroups.Perm

public section

namespace CFSG.KGroups.Native

open CFSG.Monster.B.Co2.Native

@[expose] def productsA (n : Nat) : List (List (Array Nat)) → List (Array Nat)
  | [] => [idA n]
  | T :: Ts =>
    let P := productsA n Ts
    T.flatMap fun t => P.map (compA n t)


end CFSG.KGroups.Native
