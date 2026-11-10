module

public import Certificates.Data.CFSGNative.PSL3Four.L34Aut
public meta import Certificates.Data.CFSGNative.PSL3Four.L34Aut

public section

namespace Certificates.L34TwoSig

open CFSG.PSL3Four.Native

@[expose] def b1T : Tab :=
  #[2, 0, 1, 3, 4, 9, 6, 19, 16, 10, 5, 20, 15, 11, 8, 17, 14, 12, 7, 18, 13, 30, 31, 21, 32, 33,
    26, 22, 38, 34, 23, 27, 37, 40, 41, 35, 28, 24, 36, 39, 25, 29]

@[expose] def b2T : Tab :=
  #[15, 12, 17, 6, 3, 9, 4, 18, 8, 10, 5, 2, 20, 0, 14, 13, 16, 11, 19, 7, 1, 30, 32, 21, 33, 31,
    35, 24, 28, 41, 23, 37, 40, 27, 29, 39, 36, 25, 38, 26, 22, 34]

@[expose] def bGens : Array Tab := #[b1T, b2T]


end Certificates.L34TwoSig
