module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSInputs
public import CFSG.Quasithin.Background.A312SporE8Check
public import CFSG.Quasithin.Background.A312SporShapesCheck

public section

namespace CFSG.Quasithin.A312S.HS

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.Sporadic.HS.Native (hsData)

@[expose] def hsL1 : List (Array Nat) := hsLat.sTabs ++ hsLat.mt[1]!

@[expose] def hsZ4Word : List Nat := [3, 0, 1, 3, 1, 3, 0, 1, 3, 0, 1, 0]

@[expose] def hsEWords : List (List Nat) :=
  [[2, 3, 0, 2, 3, 0], [2, 0, 1, 3, 3, 0, 3, 1, 2, 0], [1, 0, 1], [2, 1, 0, 1, 2, 0]]


@[expose] def hsE : List (Array Nat) := hsEWords.map (wordTabA hsL1.toArray hsData.n)


@[expose] def hsL2 : List (Array Nat) := hsLat.sTabs ++ hsLat.mt[2]!

@[expose] def hsWWords : List (List Nat) :=
  [[2, 2, 1, 2, 0, 1, 2, 0], [2, 2, 1, 2, 1, 0], [3, 2, 1, 2, 3, 0, 3, 1, 0]]

@[expose] def hsW : List (Array Nat) := hsWWords.map (wordTabA hsL2.toArray hsData.n)


@[expose] def hsVWords : List (List Nat) := hsWWords.map fun w => w ++ w


@[expose] def hsVMats : List (List (List Nat)) :=
  [[[1, 0, 0], [1, 1, 0], [1, 0, 1]], [[1, 1, 1], [0, 0, 1], [0, 1, 0]],
    [[1, 0, 0], [1, 0, 1], [1, 1, 0]], [[1, 0, 1], [1, 0, 0], [0, 1, 0]]]

@[expose] def hsQuot2 : List QuotGen :=
  [⟨[3, 3, 1, 1, 3], 1, 7⟩, ⟨[1, 0, 3, 2, 1, 0, 0], 1, 3⟩]

@[expose] def hsKer : List KerGen :=
  [⟨[1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0], 1, 2⟩, ⟨[0, 1, 1, 0, 1, 1], 1, 2⟩,
    ⟨[1, 0, 0, 1, 1, 0, 1, 0, 1], 1, 2⟩, ⟨[0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1], 1, 2⟩]


end CFSG.Quasithin.A312S.HS
