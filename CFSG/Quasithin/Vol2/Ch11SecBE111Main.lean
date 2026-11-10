module

public import CFSG.Quasithin.Vol2.Ch11SecBE111Core
public import CFSG.Quasithin.Background.E1ElevenLift
public import CFSG.Quasithin.Background.E1Solv

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Quasithin.A1b

theorem le_of_inEFor_sub {G : Type} [Group G] [Finite G] {i : ℕ} {Y T : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hTY : T ≤ Y) (hY : E1.InEFor i Y T) {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl ⊤ Ω) :
    Y ≤ E1.eGen i ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G)) := by
  set Ω' : Set (Subgroup G) := {B | B ∈ Ω ∧ B ≤ Y} with hΩ'def
  have hΩ' : E1.IsInvColl Y Ω' := by
    refine ⟨fun B hB => hB.2, fun B hB => hΩ.isElemAbelian B hB.1, fun B hB h hh => ?_⟩
    refine ⟨hΩ.conj B hB.1 h (Subgroup.mem_top h), fun x hx => ?_⟩
    rw [mem_conjSub_iff] at hx
    have e : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
    rw [e]
    exact Y.mul_mem (Y.mul_mem hh (hB.2 hx)) (Y.inv_mem hh)
  have hW : E1.weakClosure T Ω' = E1.weakClosure T Ω := by
    apply le_antisymm
    · exact iSup₂_le fun A hA => iSup_le fun hAT => E1.le_weakClosure hA.1 hAT
    · exact iSup₂_le fun A hA => iSup_le fun hAT =>
        E1.le_weakClosure ⟨hA, hAT.trans hTY⟩ hAT
  have hTY' : IsSylowIn 2 T Y := by
    refine ⟨hTY, hT.2.1, fun h2 => hT.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex T Y ⊤ hTY le_top
    rw [← this]
    exact Dvd.dvd.mul_right h2 _
  rw [← hY Ω' hΩ', hW]
  refine sup_le_sup ?_ (inf_le_inf_right _ le_top)
  refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
  have hTY'' : T ⊓ Y = T := inf_eq_left.mpr hTY
  have hK' : E1.IsE i Y (T ⊓ Y) A K := by rw [hTY'']; exact hK
  have hτ : E1.tauOf ⊤ T A ≤ T ⊓ Y := by
    rw [hTY'']
    exact fun t ht => ht.1
  have hS : IsSylowIn 2 (T ⊓ Y) Y := by rw [hTY'']; exact hTY'
  exact E1.le_eGen hA.1 hAT
    (E1.eight_two hT hAT (hΩ.isElemAbelian A hA.1) le_top hτ hS hK')


end CFSG.Quasithin.Vol2.Ch11.SecB
