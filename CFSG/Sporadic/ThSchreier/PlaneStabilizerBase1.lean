
module

public import CFSG.Sporadic.ThSchreier.PlaneStabilizerBase

public import CFSG.Sporadic.ThSchreier.PlaneFactsBase1
public meta import CFSG.Sporadic.ThSchreier.TransporterBase
public meta import CFSG.Sporadic.ThSchreier.UASpaceBase1
public import CFSG.Sporadic.ThSchreier.UASpaceBase1
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.LocalData
public meta import Certificates.Data.CFSGNative.Th.Base
public meta import CFSG.Sporadic.ThSchreier.CentralizerData

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] noncomputable def labGenH (l : ℕ) : J := if l = 1 then localX else localY

@[expose] noncomputable def orbElem (i : ℕ) : J :=
  if _h : 0 < i ∧ orbPar i < i then
    labGenH (orbLab i) * orbElem (orbPar i) * (labGenH (orbLab i))⁻¹
  else involT
termination_by i
decreasing_by exact _h.2

theorem orbElem_zero : orbElem 0 = involT := by
  rw [orbElem]
  simp

@[expose] noncomputable def orbSet : Set J := orbElem '' (Finset.range 819 : Set ℕ)

end CFSG.Sporadic.ThSchreier
