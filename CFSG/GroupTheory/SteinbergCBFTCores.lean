module

public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.SteinbergCBFTSCN
public import CFSG.Walter.Transitivity.OddCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup CFSG.HallHigman
open scoped commutatorElement

variable {p : ℕ} [hp : Fact p.Prime]

theorem centralizer_pCore_le_pCore {Y : Type*} [Group Y] [Finite Y]
    (hY : IsPiSeparable {q : Nat.Primes | q.val = p} Y) (hcore : pPrimeCore p Y = ⊥) :
    centralizer (pCore p Y : Set Y) ≤ pCore p Y := by
  rw [pCore_eq_piCore Y p]
  refine centralizer_piCore_le_piCore hY ?_
  rw [← hcore, pPrimeCore_eq_piCore Y p]
  rfl


end CFSG.GroupTheory.FT63ChII
