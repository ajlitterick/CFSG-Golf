module

public import CFSG.ClassicalInvolution.Balance.BootNoTripleBasic

public section

namespace CFSG.ClassicalInvolution.Balance.GoodData

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.BootRank3

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}


section Lift

variable {Y : Type*} [Group Y]

theorem exists_isElemAbelian_lift_map [Finite Y] (N : Subgroup Y) [N.Normal] (hN : Odd (Nat.card N))
    (E : Subgroup (Y ⧸ N)) (hE : IsElemAbelian 2 E) :
    ∃ H : Subgroup Y, IsElemAbelian 2 H ∧ H.map (QuotientGroup.mk' N) = E ∧
      Nat.card H = Nat.card E := by
  classical
  set φ : Y →* Y ⧸ N := QuotientGroup.mk' N with hφ
  set P : Subgroup Y := E.comap φ with hP
  have hNP : N ≤ P := fun n hn => by
    rw [hP, Subgroup.mem_comap, hφ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact E.one_mem
  have hmapP : P.map φ = E :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) E
  have : (N.subgroupOf P).Normal := Subgroup.Normal.subgroupOf inferInstance P
  have hidx : (N.subgroupOf P).index = Nat.card E := by
    have h2 := Subgroup.relIndex_comap (H := (⊥ : Subgroup (Y ⧸ N))) φ P
    rw [MonoidHom.comap_bot, hφ, QuotientGroup.ker_mk', ← hφ, hmapP,
      Subgroup.relIndex_bot_left] at h2
    exact h2
  have hcardN : Nat.card (N.subgroupOf P) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (N.subgroupOf P)) (N.subgroupOf P).index := by
    rw [hcardN, hidx, hk]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hN)
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set H : Subgroup Y := H'.map P.subtype with hH
  have hHP : H ≤ P := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcardH : Nat.card H = Nat.card E := by
    rw [← hidx, hH'.symm.index_eq_card, hH]
    exact Subgroup.card_map_of_injective (Subgroup.subtype_injective P)
  have hinj : ∀ x ∈ H, φ x = 1 → x = 1 := by
    intro x hx hx1
    obtain ⟨x', hx'H, rfl⟩ := hx
    have hxN : (x' : Y) ∈ N := (QuotientGroup.eq_one_iff _).mp hx1
    have : x' ∈ N.subgroupOf P ⊓ H' := ⟨hxN, hx'H⟩
    rw [hH'.disjoint.eq_bot] at this
    simpa using congrArg Subtype.val ((Subgroup.mem_bot).mp this)
  have hHE : H.map φ ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact hHP hx
  have hmemE : ∀ x ∈ H, φ x ∈ E := fun x hx => hHE ⟨x, hx, rfl⟩
  have hrinj : Function.Injective (φ.comp H.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have hcardmap : Nat.card (H.map φ) = Nat.card H := by
    have h1 : (φ.comp H.subtype).range = H.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1]
    exact (Nat.card_congr (MonoidHom.ofInjective hrinj).toEquiv).symm
  have hEq : H.map φ = E := Subgroup.eq_of_le_of_card_ge hHE (by omega)
  refine ⟨H, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, hEq, hcardH⟩
  · apply Subtype.ext
    have hxy := hE.1.is_comm.comm ⟨φ x, hmemE x x.2⟩ ⟨φ y, hmemE y y.2⟩
    have hxy' : φ (x : Y) * φ y = φ y * φ x := congrArg Subtype.val hxy
    have h1 : (x : Y) * y * ((y : Y) * x)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem x.2 y.2) (H.inv_mem (H.mul_mem y.2 x.2))
    have h2 := hinj _ h1 (by rw [map_mul, map_mul, map_inv, map_mul, hxy']; group)
    exact mul_inv_eq_one.mp h2
  · have h1 : x ^ 2 ∈ H := H.pow_mem hx 2
    exact hinj _ h1 (by rw [map_pow]; exact hE.2 _ (hmemE x hx))

end Lift

end CFSG.ClassicalInvolution.Balance.GoodData
