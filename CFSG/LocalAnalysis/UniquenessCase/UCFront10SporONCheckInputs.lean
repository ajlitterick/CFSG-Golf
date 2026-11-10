module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public import CFSG.Sporadic.Schreier.ONCheckSmallAuxInputs
public import CFSG.Sporadic.Schreier.ONPermArr
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAuxInputs
public meta import CFSG.Sporadic.Schreier.ONPermArr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

@[expose] def onKPerm (n : ℕ) (t : Array ℕ) : Equiv.Perm (Fin n) :=
  if h : pisInv n t (pinvCand n t) = true ∧ pisInv n (pinvCand n t) t = true then
    { toFun := fun i => ⟨t[i.val]!, (pisInv_spec h.1 i.2).1⟩
      invFun := fun i => ⟨(pinvCand n t)[i.val]!, (pisInv_spec h.2 i.2).1⟩
      left_inv := fun i => Fin.ext (pisInv_spec h.1 i.2).2
      right_inv := fun i => Fin.ext (pisInv_spec h.2 i.2).2 }
  else 1

abbrev p120 (t : Array ℕ) : Equiv.Perm (Fin 120) := onKPerm 120 t


@[expose] def onKY5 : Array ℕ :=
  #[106, 118, 20, 115, 54, 18, 95, 73, 39, 41, 36, 50, 9, 82, 96, 5, 99, 68, 92, 35, 47, 84, 53,
    113, 105, 29, 69, 57, 2, 34, 1, 44, 100, 62, 11, 7, 102, 8, 27, 22, 80, 94, 107, 30, 61, 60, 13,
    88, 19, 91, 25, 119, 64, 37, 16, 14, 72, 52, 21, 10, 55, 66, 93, 74, 38, 89, 86, 12, 77, 42, 23,
    26, 117, 48, 103, 56, 43, 3, 46, 111, 32, 59, 108, 75, 112, 65, 31, 58, 28, 51, 70, 63, 101, 24,
    67, 79, 45, 116, 90, 109, 114, 15, 81, 49, 97, 33, 104, 71, 78, 4, 6, 110, 87, 98, 40, 17, 0,
    83, 76, 85]

@[expose] def onKY7 : Array ℕ :=
  #[0, 88, 4, 107, 21, 44, 114, 87, 86, 72, 8, 39, 105, 99, 45, 53, 38, 16, 80, 22, 95, 89, 56, 27,
    101, 49, 35, 67, 59, 6, 70, 117, 36, 13, 66, 103, 55, 100, 60, 69, 58, 34, 30, 115, 71, 113,
    111, 40, 112, 26, 57, 74, 78, 20, 63, 76, 65, 116, 108, 91, 77, 12, 104, 33, 82, 42, 50, 11,
    102, 84, 19, 10, 18, 48, 32, 5, 93, 3, 31, 62, 7, 97, 54, 46, 23, 41, 75, 92, 28, 79, 81, 68, 9,
    51, 25, 24, 15, 98, 73, 64, 47, 96, 1, 110, 2, 119, 43, 17, 109, 37, 94, 29, 90, 52, 118, 61,
    85, 14, 83, 106]

@[expose] def onKD : Array (Array ℕ) := #[
  #[0, 1, 2, 3, 4, 6, 5, 7, 8, 9, 25, 26, 12, 13, 28, 15, 16, 18, 17, 20, 19, 21, 22, 31, 30, 10,
    11, 27, 14, 29, 24, 23],
  #[2, 7, 0, 12, 13, 14, 28, 1, 21, 22, 23, 30, 3, 4, 5, 27, 29, 20, 19, 18, 17, 8, 9, 10, 26, 31,
    24, 15, 6, 16, 11, 25],
  #[2, 7, 0, 12, 13, 28, 14, 1, 21, 22, 31, 24, 3, 4, 6, 27, 29, 19, 20, 17, 18, 8, 9, 25, 11, 23,
    30, 15, 5, 16, 26, 10],
  #[3, 8, 12, 0, 15, 5, 6, 21, 1, 16, 10, 11, 2, 27, 14, 4, 9, 17, 18, 19, 20, 7, 29, 23, 24, 25,
    26, 13, 28, 22, 30, 31],
  #[3, 8, 12, 0, 15, 6, 5, 21, 1, 16, 25, 26, 2, 27, 28, 4, 9, 18, 17, 20, 19, 7, 29, 31, 30, 10,
    11, 13, 14, 22, 24, 23],
  #[12, 21, 3, 2, 27, 14, 28, 8, 7, 29, 23, 30, 0, 15, 5, 13, 22, 20, 19, 18, 17, 1, 16, 10, 26, 31,
    24, 4, 6, 9, 11, 25],
  #[12, 21, 3, 2, 27, 28, 14, 8, 7, 29, 31, 24, 0, 15, 6, 13, 22, 19, 20, 17, 18, 1, 16, 25, 11, 23,
    30, 4, 5, 9, 26, 10]]

@[expose] def onKE : Array ℕ :=
  #[0, 1, 2, 3, 4, 6, 5, 7, 8, 9, 25, 26, 12, 13, 28, 15, 16, 18, 17, 20, 19, 21, 22, 31, 30, 10,
    11, 27, 14, 29, 24, 23]


end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK
