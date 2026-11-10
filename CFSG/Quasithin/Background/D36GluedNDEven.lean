module

public import CFSG.Quasithin.Background.D36GluedNDBase
import CFSG.Quasithin.Background.D36GluedNDOut
import CFSG.Quasithin.Background.F918Z4bL2
import CFSG.Quasithin.Background.F918Z4c1PSL
import CFSG.Quasithin.Background.F918Z4c2Main

public section

namespace CFSG.Quasithin

open CFSG.GorensteinWalter

theorem conj_injective_of_simple {G : Type} [Group G] (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  have hc : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have : a ∈ Subgroup.center G := by rw [h]; trivial
      exact ((Subgroup.mem_center_iff.mp this) b).symm
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun φ : MulAut G => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [hc] at this
  exact Subgroup.mem_bot.mp this


namespace NDSetup


end NDSetup

end CFSG.Quasithin
