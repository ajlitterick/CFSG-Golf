module

public import CFSG.Certificates.CosetTableAction
public import CFSG.Certificates.CosetTableColumns
public import Certificates.Data.CFSGNative.CosetTable.ActionNative

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}


@[expose] def orderCheck (ws : List (List (Fin m × Bool))) (S : List ℕ) (k cap n : ℕ)
    (words : List (List (Fin m × Bool) × ℕ)) (fuel : ℕ) : Bool :=
  let P := colParamsShort ws ((subsetOf m S).map fun x => [(x, true)]) k
  let st := enumerateHLT P cap
  (!st.overflow && st.complete P.L && st.liveCount == n) &&
    invConsistentNative P.L (colInv ws) st && relsClosedNative P.L st (colCodes ws ws) &&
    words.all fun p => cycleLength P.L st.tab (p.1.map (colCode ws)) 1 fuel == p.2


end CFSG.CosetTable
