module

public import Certificates.Data.CFSGNative.Fi22.Classes

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.FrameJ

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi22.Native

set_option compiler.extract_closed false

@[expose] def fjDLeaf (a A B : Table) : Bool :=
  let P := compT 3510 A B
  invoOK 3510 P && !idOK 3510 P && order3OK 3510 (compT 3510 P a)


end CFSG.EvenSporadicStandard.TwoFi22.FrameJ
