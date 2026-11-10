module

public import Certificates.Data.CFSGNative.PropA.Check

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA.Data

open CFSG.Sporadic.Th.Native CFSG.EvenSporadicStandard.M12Std.PropA.Native

@[expose] def tabA : Table :=
  #[3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5, 15, 13, 21, 12, 22, 23, 18, 19, 20, 14, 16, 17, 24,
  25, 26, 27]

@[expose] def tabB : Table :=
  #[7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10, 17, 20, 13, 12, 19, 15, 22, 21, 14, 16, 23, 18, 24,
  25, 26, 27]

@[expose] def tabG1 : Table :=
  #[12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 25,
  24, 27, 26]

@[expose] def tabG2 : Table :=
  #[12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 25,
  26, 27, 24]

@[expose] def tabT : Table :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26,
  27, 24, 25]

@[expose] def wx0 : Word :=
  [1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2]


end CFSG.EvenSporadicStandard.M12Std.PropA.Data
