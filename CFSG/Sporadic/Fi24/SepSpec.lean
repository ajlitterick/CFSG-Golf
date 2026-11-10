
module

public import CFSG.Sporadic.Fi24.SepSpecBase
import all CFSG.Sporadic.Fi24.SepSpecBase


public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Fi24.Native

open Matrix CFSG.F3.Native

section Algebra

variable (mats : Array (Array W))

variable {mats}

theorem MatsOK.get {mats : Array (Array W)} (h : MatsOK mats) {i : ℕ} (hi : i < mats.size) :
    canonRows 781 (mats[i]?.getD #[]) = true := by
  have := h i hi
  rwa [getElem!_pos mats i hi, ← Option.getD_some (a := mats[i]) (b := #[]),
    ← Array.getElem?_eq_getElem hi] at this


end Algebra


end CFSG.Sporadic.Fi24.Native
