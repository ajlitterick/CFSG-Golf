module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.H13.A5Producer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

theorem fix_pa_eq : ∀ x : W5, pact pa x = x → ∃ u : W5, x = u * pact pa u := by
  decide +kernel

theorem fixed_pa_pb : ∀ x : W5, pact pa x = x → pact pb x = x → x = 1 ∨ x = W4 := by
  decide +kernel

theorem W4_eq : pact pa (Multiplicative.ofAdd (e2 0 1)) = Multiplicative.ofAdd (e2 0 1) ∧
    W4 = Multiplicative.ofAdd (e2 0 1) * pact pb (Multiplicative.ofAdd (e2 0 1)) := by
  decide +kernel

theorem fix_pa_pb_eq (x : W5) (ha : pact pa x = x) (hb : pact pb x = x) :
    ∃ y : W5, pact pa y = y ∧ x = y * pact pb y := by
  rcases fixed_pa_pb x ha hb with rfl | rfl
  · exact ⟨1, map_one _, by rw [map_one, one_mul]⟩
  · exact ⟨_, W4_eq.1, W4_eq.2⟩

theorem K4_facts : pa * pa = 1 ∧ pb * pb = 1 ∧ pb * pa * pb⁻¹ * pa⁻¹ = 1 := by
  decide

theorem InK4_cases : ∀ σ : Equiv.Perm (Fin 5), InK4 σ →
    σ = 1 ∨ σ = pa ∨ σ = pb ∨ σ = pa * pb := by
  decide +kernel


namespace Setting


end Setting

end CFSG.GH74.QTGen4.U42
