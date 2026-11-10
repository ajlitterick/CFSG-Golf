module

public import Certificates.Data.Smith1979W3.CensusData

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

@[expose] def censusBase (minus : Bool) (_ : Unit := ()) : Bool :=
  let D := grpData minus ()
  let Ld := ldata minus ()
  censusBaseOf minus D Ld


end CFSG.GF2Type.Smith1979W3.Cert690

end
