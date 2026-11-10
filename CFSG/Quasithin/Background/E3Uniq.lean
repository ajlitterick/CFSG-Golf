module

public import CFSG.Quasithin.Background.E3Prop

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section Uniq

variable {G : Type u} [Group G] [Finite G] {V S H M : Subgroup G}

theorem e3_21_comm (hV : IsElemAbelian 2 V) (hVN : S ≤ Subgroup.normalizer (V : Set G)) {i : ℕ}
    (hia : i + aParam (autI hV ⊤) < sParam hV) : ⁅V, wClos V i S⁆ = ⊥ := by
  refine e3_18_comm hV (H := S) le_rfl hVN hV ?_
  have := aParam_mono (autI_mono hV (le_top : S ≤ ⊤))
  omega

theorem e3_21_le (hV : IsElemAbelian 2 V) (hVN : S ≤ Subgroup.normalizer (V : Set G)) {i : ℕ}
    (hia : i + aParam (autI hV ⊤) < sParam hV) :
    wClos V i S ≤ S ⊓ Subgroup.centralizer (V : Set G) := by
  refine le_inf (wClos_le i S) ?_
  have h := e3_21_comm hV hVN hia
  rw [Subgroup.commutator_comm] at h
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h


end Uniq

end E3

end CFSG.Quasithin
