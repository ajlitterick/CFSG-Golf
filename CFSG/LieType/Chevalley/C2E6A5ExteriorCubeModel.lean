module

public import CFSG.LieType.Chevalley.C2E6A5CubeTwist

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.ExteriorCube exteriorPower Set Matrix
  CFSG.LocalAnalysis.ComponentInitial

theorem mem_scalars_iff (z : SpecialLinearGroup (Fin 6) K) :
    z ∈ LinearFlag.scalars 6 K ↔
      ∃ l : Kˣ, (z : Matrix (Fin 6) (Fin 6) K) = scalar (Fin 6) (l : K) := by
  rw [LinearFlag.mem_scalars]
  constructor
  · rintro ⟨c, -, hc⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, units_pow_three, one_pow], hc⟩


end CFSG.LieType.Chevalley.C2E6Std
