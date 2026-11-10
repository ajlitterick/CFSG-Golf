module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic
public import CFSG.Quasithin.AppendixH.H9.ConjTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {n : ℕ}

@[expose] def ez (m : ℕ) : Fin (m + 1) → ZMod 2 := Pi.single 0 1


end CFSG.ASVolI.ChH
