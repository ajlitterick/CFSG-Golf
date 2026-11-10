
module

public import CFSG.Sporadic.Ly.Setup

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native Matrix CFSG.Certificates

abbrev lyN : ℕ := 8835156

@[expose] def lyU : Matrix (Fin 111) (Fin 7) (ZMod 5) := keyU rootKey

@[expose] def lyS : Matrix (Fin 7) (Fin 7) (ZMod 5) := keyC rootKey

@[expose] def lyF : Matrix (Fin 111) (Fin 111) (ZMod 5) := mF

@[expose] def lyE : Matrix (Fin 111) (Fin 111) (ZMod 5) := lyU * lyS * lyUᵀ * lyF


end CFSG.RankThree.Native
