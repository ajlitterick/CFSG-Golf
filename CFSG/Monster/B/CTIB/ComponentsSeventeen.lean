module

public import CFSG.Monster.B.CTIB.Rank2168Final
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Monster.B CFSG.LieType.Chevalley.C2E6Std
open CFSG.Sporadic.Co2Inv (co2_involution_input)

theorem quotientCenter_map_equiv {G H : Type*} [Group G] [Group H] (Ψ : G ≃* H)
    (K : Subgroup G) :
    Nonempty (K ⧸ Subgroup.center K ≃*
      K.map Ψ.toMonoidHom ⧸ Subgroup.center (K.map Ψ.toMonoidHom)) :=
  ⟨QuotientGroup.congr _ _ (K.equivMapOfInjective Ψ.toMonoidHom Ψ.injective)
    (Subgroup.map_center_eq (K.equivMapOfInjective Ψ.toMonoidHom Ψ.injective))⟩

theorem center_eq_bot_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (hq : CFSG.IsQuasisimple G) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hx : x ∈ Subgroup.center G := h ▸ Subgroup.mem_top x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hx y]

theorem involution_local_components_simple_quotient_divisible_by_seventeen
    {T : Type*}
    [Group T] (hT : Nonempty (T ≃* NativeSporadic.B)) :
    ∀ t : T, orderOf t = 2 → ∀ K : Subgroup (Subgroup.centralizer {t}), CFSG.IsComponent K →
      IsSimpleGroup (K ⧸ Subgroup.center K) ∧
      (Nonempty (K ⧸ Subgroup.center K ≃* stdGroup) ∨
        Nonempty (K ⧸ Subgroup.center K ≃* adjointGroup Tag.F4 (ZMod 2))) ∧
      17 ∣ Nat.card (K ⧸ Subgroup.center K) := by
  intro t ht K hK
  obtain ⟨e⟩ := hT
  have hs : orderOf ((e.trans iotaEquiv) t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  have hK' := CFSG.LocalCores.isComponent_map_mulEquiv (centralizerEquiv (e.trans iotaEquiv) t) hK
  obtain ⟨eQ⟩ := quotientCenter_map_equiv (centralizerEquiv (e.trans iotaEquiv) t) K
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := four_classes co2_involution_input hs
  have hr := rank_beta_conj hc
  obtain ⟨h1, h0, h5, h3⟩ := rank_four
  refine ⟨hK.1.2.1, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · rw [h1] at hr
    obtain ⟨K₀, -, hU, -, -, ⟨θ⟩, -, h17⟩ := native_rank_1860_unique_component_final _ hs hr
    obtain rfl := hU _ hK'
    refine ⟨Or.inl ⟨eQ.trans θ⟩, ?_⟩
    rw [Nat.card_congr eQ.toEquiv]
    exact h17
  · rw [h0] at hr
    exact absurd hK' ((native_rank_2048_centralizer_has_no_components _ hs hr).elim
      fun _ hc => hc.2.2.2.elim fun _ hQ => hQ.2.2.2.2.2.2.2 _)
  · rw [h5] at hr
    obtain ⟨K₀, hK₀, hU, hS, ⟨θ⟩, -, h17⟩ :=
      native_rank_2158_distance_three_product_final.2.1 _ hs hr
    obtain rfl := hU _ hK'
    have hbot := @center_eq_bot_of_isSimpleGroup _ _ hS hK₀.1
    have e₀ := (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    refine ⟨Or.inr ⟨(eQ.trans e₀).trans θ⟩, ?_⟩
    rw [Nat.card_congr (eQ.trans e₀).toEquiv]
    exact h17
  · rw [h3] at hr
    exact absurd hK' ((native_rank_2168_centralizer_has_no_components _ hs hr).2.2 _)

end CFSG.Monster.B.CTIB
