module

public import CFSG.Quasithin.H13.GoldschmidtC137L3Fin

public section

namespace CFSG.ASVolI

open CFSG.Quasithin.L3 CFSG.Quasithin.H13.U3.GC137

set_option maxRecDepth 100000 in
theorem burnsideC137_center_triv : ∀ g : Γ, (∀ h : Γ, g * h = h * g) → g = 1 := by
  decide +kernel

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 100000 in
theorem burnsideC137_BS_pair : ∀ S : Finset Vec, IsPlane S → ∀ S' : Finset Vec, IsPlane S' →
    S ≠ S' → ∃ a : Γ, (∀ v ∈ S, act a v = v) ∧ ∃ b : Γ, (∀ v ∈ S', act b v = v) ∧
      IsOrd3 (a * b) := by
  decide +kernel


end CFSG.ASVolI
