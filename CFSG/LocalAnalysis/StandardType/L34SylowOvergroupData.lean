module

public import Certificates.Data.CFSGNative.PSL3Four.L34Aut
public import Std.Data.HashSet

public section

namespace CFSG.StandardType.L34Sylow

open CFSG.PSL3Four.Native

@[expose] def pT : Tab :=
  #[15, 12, 17, 6, 3, 9, 4, 18, 8, 10, 5, 2, 20, 0, 14, 13, 16, 11, 19, 7, 1, 30, 32, 21, 33, 31,
    35, 24, 28, 41, 23, 37, 40, 27, 29, 39, 36, 25, 38, 26, 22, 34]

@[expose] def qT : Tab :=
  #[2, 0, 1, 3, 4, 9, 6, 19, 16, 10, 5, 20, 15, 11, 8, 17, 14, 12, 7, 18, 13, 30, 31, 21, 32, 33,
    26, 22, 38, 34, 23, 27, 37, 40, 41, 35, 28, 24, 36, 39, 25, 29]

@[expose] def aSixGen1T : Tab :=
  #[1, 10, 14, 6, 18, 0, 4, 3, 2, 12, 16, 8, 20, 9, 17, 13, 5, 11, 7, 19, 15, 30, 26, 38, 34, 22,
    27, 37, 23, 40, 28, 24, 41, 35, 29, 39, 36, 25, 21, 32, 31, 33]

@[expose] def aSixGen2T : Tab :=
  #[1, 2, 3, 4, 0, 8, 20, 12, 16, 14, 10, 18, 6, 17, 5, 13, 9, 11, 15, 7, 19, 36, 28, 40, 22, 32,
    26, 23, 31, 41, 27, 33, 38, 24, 29, 39, 25, 30, 21, 34, 37, 35]

@[expose] def aSixGen3T : Tab :=
  #[1, 10, 18, 14, 6, 0, 3, 2, 4, 11, 19, 15, 7, 12, 8, 20, 16, 9, 13, 5, 17, 30, 26, 34, 22, 38,
    27, 40, 37, 23, 29, 25, 39, 36, 21, 33, 32, 31, 28, 35, 24, 41]

@[expose] def aSixGen4T : Tab :=
  #[1, 2, 3, 4, 0, 9, 13, 5, 17, 19, 7, 15, 11, 16, 12, 20, 8, 6, 18, 10, 14, 31, 21, 33, 30, 32,
    26, 41, 36, 23, 29, 40, 34, 24, 27, 39, 35, 22, 28, 38, 37, 25]

@[expose] def aSixGen5T : Tab :=
  #[1, 2, 3, 4, 0, 15, 11, 19, 7, 5, 17, 9, 13, 10, 14, 6, 18, 20, 8, 16, 12, 23, 29, 35, 38, 32,
    26, 36, 41, 31, 21, 25, 22, 24, 28, 39, 33, 34, 27, 30, 37, 40]

@[expose] def aSixGen6T : Tab :=
  #[1, 13, 17, 5, 9, 4, 3, 0, 2, 6, 10, 14, 18, 20, 8, 16, 12, 11, 19, 15, 7, 39, 26, 37, 32, 24,
    21, 40, 41, 38, 27, 35, 31, 22, 29, 25, 36, 30, 28, 33, 23, 34]


@[expose] def pGens : Array Tab := #[pT, qT]

@[expose] def pGensWith (r : Tab) : Array Tab := #[pT, qT, r]

@[expose] def pGensWith2 (r g : Tab) : Array Tab := #[pT, qT, r, g]

@[expose] def mRs : Array Tab :=
  #[aSixGen1T, aSixGen2T, aSixGen3T, aSixGen4T, aSixGen5T, aSixGen6T]


end CFSG.StandardType.L34Sylow
