module

public import CFSG.GF2Type.Smith1979.IdxFourModelChainInputs
public import CFSG.GF2Type.Smith1979.IdxFourModelOrbitInputs

public section

namespace CFSG.GF2Type.Smith1979.IdxFour.E0Chk

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour.Orb


@[expose] def sGensE0 : List (Array ℕ) :=
  [#[2, 4, 1, 8, 16, 32, 128, 256, 64, 512, 1024, 2048],
   #[1448, 2683, 2685, 1441, 2671, 1417, 3990, 1193, 1321, 3542, 425, 2006],
   #[1, 8, 2, 4, 16, 32, 64, 512, 128, 256, 1024, 2048],
   #[2, 1, 4, 8, 32, 16, 128, 64, 256, 512, 2048, 1024],
   #[1, 2, 4, 8, 1040, 2048, 64, 128, 256, 512, 16, 2080]]


@[expose] def dCodes : List ℕ := [0, 15, 960, 975]


end CFSG.GF2Type.Smith1979.IdxFour.E0Chk
