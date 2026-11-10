module

public import CFSG.Sporadic.HeldB.InnerCheckInputs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative

public section

namespace CFSG.Sporadic.HeldB.Mixed
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Monster.B.Co2.Native

@[expose] def generatorIndices : Array Nat := #[1,2,3,8]

@[expose] def mixedWords : List (List Int) :=
  [[1,2,3,2],
   [1,-4,1,2,4,4,3,4],
   [1,-4,1,2,1,-4,1,2],
   [1,4,1,-4,3,4,2],
   [3,-4,1,2,1,2,4,3],
   [3,-4,1,3,4,3],
   [2,1,3,-4,-4,2,1,4],
   [1,2,1,-4,-4,2,1,4]]


end CFSG.Sporadic.HeldB.Mixed
