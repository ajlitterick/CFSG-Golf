module

public import CFSG.HardMathSupport.Lang.AnisoE6.E6InF4
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Defs
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Sylow

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem not_normalizesRIn_comap_of_map {r : ℕ} {F M : Type*} [Group F] [Group M] (ι : F →* M)
    (hι : Function.Injective ι) {E₀ : Subgroup M} (g : M) (hn : ¬ NormalizesRIn r E₀)
    (E₃ : Subgroup F) (hE₃ : E₃.map ι = E₀.map (MulAut.conj g).toMonoidHom) :
    ¬ NormalizesRIn r E₃ := by
  rintro ⟨R₃, hR1, hRp, hRn⟩
  apply hn
  set R₆ : Subgroup M := R₃.map ι with hR₆
  have hR₆1 : R₆ ≠ ⊥ := fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective R₃ hι).mp h)
  have hR₆p : IsPGroup r R₆ :=
    hRp.of_surjective (ι.subgroupMap R₃) (ι.subgroupMap_surjective R₃)
  have hnorm₆ : E₃.map ι ≤ Subgroup.normalizer (R₆ : Set M) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_conj_eq_iff_mem_normalizer]
    have hxn := (map_conj_eq_iff_mem_normalizer R₃ x).2 (hRn hx)
    have hcomp : (MulAut.conj (ι x)).toMonoidHom.comp ι = ι.comp (MulAut.conj x).toMonoidHom := by
      ext z
      simp [MulAut.conj_apply]
    rw [hR₆, Subgroup.map_map, hcomp, ← Subgroup.map_map, hxn]
  refine ⟨R₆.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · exact fun h =>
      hR₆1 ((Subgroup.map_eq_bot_iff_of_injective R₆ (MulAut.conj g⁻¹).injective).mp h)
  · exact hR₆p.of_surjective ((MulAut.conj g⁻¹).toMonoidHom.subgroupMap R₆)
      ((MulAut.conj g⁻¹).toMonoidHom.subgroupMap_surjective R₆)
  · intro y hy
    rw [mem_normalizer_map_conj_iff, inv_inv]
    exact hnorm₆ (hE₃ ▸ Subgroup.mem_map_of_mem _ hy)

section Embedding


noncomputable def e6FixedF4 (K : Type) [Field K] : Subgroup (adjointGroup .E6 K) :=
  (CFSG.HardMathSupport.Lang.AnisoE6.exists_f4_fixed_in_e6_field K).choose

noncomputable def e6FixedF4Equiv (K : Type) [Field K] : adjointGroup .F4 K ≃* e6FixedF4 K :=
  (CFSG.HardMathSupport.Lang.AnisoE6.exists_f4_fixed_in_e6_field K).choose_spec.choose

noncomputable def e6F4Embed (K : Type) [Field K] : adjointGroup .F4 K →* adjointGroup .E6 K :=
  (e6FixedF4 K).subtype.comp (e6FixedF4Equiv K).toMonoidHom

theorem e6F4Embed_injective (K : Type) [Field K] : Function.Injective (e6F4Embed K) :=
  Subtype.val_injective.comp (e6FixedF4Equiv K).injective

theorem mem_range_e6F4Embed (K : Type) [Field K] (x : adjointGroup .E6 K) :
    x ∈ (e6F4Embed K).range ↔ x ∈ e6FixedF4 K := by
  constructor
  · rintro ⟨y, rfl⟩
    exact (e6FixedF4Equiv K y).2
  · intro hx
    exact ⟨(e6FixedF4Equiv K).symm ⟨x, hx⟩, by simp [e6F4Embed]⟩

theorem card_e6FixedF4 (K : Type) [Field K] [Finite K] :
    Nat.card (e6FixedF4 K) = CFSG.Open.ordF4 (Nat.card K) := by
  rw [Nat.card_congr (e6FixedF4Equiv K).symm.toEquiv,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]

theorem index_e6FixedF4 (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 2) :
    (e6FixedF4 K).index = Nat.card K ^ 12 * (Nat.card K ^ 9 - 1) * (Nat.card K ^ 5 - 1) := by
  have hcard := Subgroup.card_mul_index (e6FixedF4 K)
  rw [card_e6FixedF4, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6,
    ordE6_eq_ordF4_mul_of_mod_two hK] at hcard
  have hpos : 0 < CFSG.Open.ordF4 (Nat.card K) := by
    rw [← card_e6FixedF4]
    exact Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos hcard

theorem not_dvd_three_index_e6FixedF4 (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 2) :
    ¬ 3 ∣ (e6FixedF4 K).index := by
  rw [index_e6FixedF4 K hK]
  exact not_dvd_three_mod_two hK

theorem exists_conj_into_e6F4_two (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    {E₀ : Subgroup (adjointGroup .E6 K)} (hexp : ∀ x ∈ E₀, x ^ 3 = 1) :
    ∃ g : adjointGroup .E6 K, ∀ x ∈ E₀, g * x * g⁻¹ ∈ (e6F4Embed K).range := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 E₀ := fun x => ⟨1, by
    rw [pow_one]
    apply Subtype.ext
    simpa using hexp x x.2⟩
  obtain ⟨c, hc⟩ :=
    exists_conj_le_of_not_dvd_index (e6FixedF4 K) (not_dvd_three_index_e6FixedF4 K hK) hP
  refine ⟨c⁻¹, fun x hx => ?_⟩
  rw [mem_range_e6F4Embed]
  simpa [inv_inv] using hc x hx

section Glue


end Glue

end Embedding

end CFSG.LieType.SeitzGeneration.ExcHighThree

end
