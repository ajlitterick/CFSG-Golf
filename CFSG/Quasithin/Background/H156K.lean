module

public import CFSG.Quasithin.Background.H158KT
public import CFSG.Quasithin.Background.H158UTrio

public section

namespace CFSG.Quasithin.H156

open CFSG.Quasithin.H158U CFSG.Quasithin.H158T CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.LU CFSG.Monster.Code CFSG.Quasithin CFSG.Open


@[expose] noncomputable def Kperm : Subgroup (Equiv.Perm (Fin 24)) :=
  ((img11 trQ ⊓ centSub UT).comap rhoM24).map AutPerm.subtype


theorem card_img11 {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (hΓ : Γ ≤ AutPerm) : Nat.card ↥(img11 Γ) = Nat.card ↥Γ := by
  rw [img11, Subgroup.card_map_of_injective (rho11_injective AutPerm le_rfl),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΓ).toEquiv]

theorem img11_Kperm : img11 Kperm = img11 trQ ⊓ centSub UT := by
  have hsub : Kperm.subgroupOf AutPerm = (img11 trQ ⊓ centSub UT).comap rhoM24 :=
    Subgroup.comap_map_eq_self_of_injective AutPerm.subtype_injective _
  rw [img11, hsub]
  refine Subgroup.map_comap_eq_self ?_
  rw [range_rho11_eq_img11 AutPerm le_rfl]
  exact inf_le_left.trans (img11_trQ_le.trans inf_le_left)


theorem stabUTP_eq_genT :
    genT = stabUTP := by
  obtain ⟨hcS, hSP, hQc⟩ := CFSG.Quasithin.H158U.stab_facts
  have h1 : 6 * Nat.card ↥trQ ≤ Nat.card ↥genT :=
    mul_card_le_of_cosets trQ_le_genT twP tw_mem_genT
      fun i j h => tw_distinct i j (trQ_le_trioP0 h)
  exact Subgroup.eq_of_le_of_card_ge (genT_le.trans inf_le_left) (by omega)


section Generic

variable {V : Type*} [CommGroup V] (U : Subgroup V) {K : Type*} [Group K] (f : K →* MulAut V)
  (X : Subgroup (MulAut V)) (hfX : ∀ k, f k ∈ X) (hf : ∀ k, f k ∈ stabSub U)


end Generic

theorem img11_trQ_stab : img11 trQ ≤ stabSub UT := img11_trQ_le.trans inf_le_right


end CFSG.Quasithin.H156
