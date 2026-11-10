
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase1

public import CFSG.Sporadic.Th.Simple
public import CFSG.Perm.CentralizerOrbit
public import CFSG.Sporadic.Ly.ThreeBCount

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped Matrix Pointwise

section Facts

variable {c' : ℕ} (hC : CertFacts c')
include hC

theorem card_L : Nat.card L = 54 := by
  have hT := treeData_q1 hC
  have horb := hT.card_orbit
  have hstab : MulAction.stabilizer L (⟨2, hT.r_lt⟩ : Fin nX) = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    rw [MulAction.mem_stabilizer_iff] at hl
    have h2 : idx nX (l : J) 2 = 2 := by
      have := idx_val (l : J) (⟨2, hT.r_lt⟩ : Fin nX)
      rw [show (l : J) • (⟨2, hT.r_lt⟩ : Fin nX) = l • (⟨2, hT.r_lt⟩ : Fin nX) from rfl, hl]
        at this
      exact this
    have := L_fix_two_eq_one hC l l.2 h2
    exact (Subgroup.mem_bot).2 (Subtype.ext this)
  have h := Subgroup.card_mul_index (MulAction.stabilizer L (⟨2, hT.r_lt⟩ : Fin nX))
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hstab, Subgroup.card_bot, one_mul] at h
  rw [← h]
  exact horb


end Facts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
