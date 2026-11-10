module

public import Certificates.Data.CFSGNative.DepFrame.Check

public section

namespace CFSG.DepFrame

open CFSG.TwoNodeSmall CFSG.ReflExt CFSG.NineAll

set_option compiler.extract_closed false


@[expose] def verifyRepM (P0 : Pt) (cand : List Refl) (rp : NRep) : Bool :=
  match rp.kind with
  | .w (.weyl _) => false
  | _ => verifyRepD P0 cand rp

@[expose] def verifyAllM (P0 : Pt) (T : NTables) : Bool :=
  wfCheck P0 && vFixN P0 && vRootsN P0 T &&
  (let cand := candOfN P0 T
   vCover1 P0 T cand && T.orb1.all (entry1OK P0 T) && T.reps.all (verifyRepM P0 cand) &&
   T.orb1.all (centEntryOK P0 T))


end CFSG.DepFrame

end
