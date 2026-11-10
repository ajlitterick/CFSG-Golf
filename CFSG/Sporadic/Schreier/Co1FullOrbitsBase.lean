
module

public import CFSG.Sporadic.Schreier.Co1FullOrbCheckBase

@[expose] public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD toVecD_injective)
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix

local notation "gaOrbit" => kOrbit GA

local notation "rootOrbit" k:max => kOrbit GA (toVecD 24 (Native.fullRoot k))

theorem fullOrb_two :
    Native.fullOrb 2 = CFSG.Sporadic.SmallF2.O CFSG.Sporadic.Co1.Native.co1Data := by
  have hd : CFSG.Sporadic.Co1.Native.co1Data.d = 24 := rfl
  have hv : CFSG.Sporadic.Co1.Native.co1Data.v0 = Native.fullRoot 2 := rfl
  have hn : CFSG.Sporadic.Co1.Native.co1Data.n = Native.fullSize 2 := rfl
  unfold Native.fullOrb CFSG.Sporadic.SmallF2.O CFSG.Sporadic.SmallF2.Native.VecData.orbit
  rw [hd, hv, hn]

theorem co1X_eq_enumSet : co1X = enumSet (Native.fullOrb 2) 98280 := by
  rw [enumSet, fullOrb_two, co1X]


theorem actsBy_A₁ :
    ActsBy A₁ CFSG.Sporadic.Co1.Native.co1Data.colsA := MRep.actsBy rep_A₁

theorem actsBy_A₂ :
    ActsBy A₂ CFSG.Sporadic.Co1.Native.co1Data.colsB := MRep.actsBy rep_A₂


theorem fullSize_inj {j k : ℕ} (hj : j < 4) (hk : k < 4) (h : Native.fullSize j = Native.fullSize k) :
    j = k := by
  revert h
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

theorem mem_or_disjoint {S : Submodule (ZMod 2) Vec24}
    (hS : ∀ g ∈ GA, ∀ v ∈ S, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ S)
    {u w w' : Vec24} (hw : w ∈ gaOrbit u) (hw' : w' ∈ gaOrbit u) (hwS : w ∈ S) : w' ∈ S := by
  rw [← kOrbit_eq_of_mem hw] at hw'
  obtain ⟨g, hg, rfl⟩ := hw'
  exact hS g hg w hwS

end CFSG.Sporadic.Co1Schreier
