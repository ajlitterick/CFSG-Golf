module

public import CFSG.CharacterTheory.Wreathed.CentralProduct
public import CFSG.GH74.GLS.Bg.Local.Lemma1621

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem two_smul_eq_zero_half_quarter (l : ℕ) (hl : 0 < l) (c : ZMod (4 * l)) :
    2 • c = 0 ↔ c = 0 ∨ c = (2 * l : ℕ) := by
  let : NeZero (4 * l) := ⟨by omega⟩
  have hlt := ZMod.val_lt c
  have heq : 2 • c = ((2 * c.val : ℕ) : ZMod (4 * l)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]
  have hdiv (t : ℕ) : 4 * l ∣ 2 * t ↔ 2 * l ∣ t := by
    rw [show 4 * l = 2 * (2 * l) by omega,
      Nat.mul_dvd_mul_iff_left (by decide : 0 < (2 : ℕ))]
  rw [heq, ZMod.natCast_eq_zero_iff, hdiv c.val]
  constructor
  · rintro ⟨k, hk⟩
    have hklt : k < 2 := by nlinarith
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · left
      have hz : c.val = 0 := by simpa using hk
      rw [← ZMod.natCast_zmod_val c, hz, Nat.cast_zero]
    · right
      have hz : c.val = 2 * l := by simpa using hk
      rw [← ZMod.natCast_zmod_val c, hz]
  · rintro (rfl | rfl)
    · simp
    · rw [ZMod.val_natCast_of_lt (by omega)]

theorem quaternionEight_noncentral_square (q : QuaternionGroup 2)
    (hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2) : q ^ 2 = QuaternionGroup.a 2 :=
  (show ∀ q : QuaternionGroup 2,
    q ≠ 1 ∧ q ≠ QuaternionGroup.a 2 → q ^ 2 = QuaternionGroup.a 2 by decide) q hq

theorem quaternionEight_noncentral_order (q : QuaternionGroup 2)
    (hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2) : orderOf q = 4 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hs := quaternionEight_noncentral_square q hq
  have hn : q ^ 2 ≠ 1 := by
    rw [hs]
    decide
  have hf : q ^ 4 = 1 := by
    calc q ^ 4 = (q ^ 2) ^ 2 := by rw [← pow_mul]
         _ = (QuaternionGroup.a 2) ^ 2 := by rw [hs]
         _ = 1 := by decide
  exact orderOf_eq_prime_pow (p := 2) (n := 1) hn hf


private theorem eq_of_orderOf_eq_two_of_isCyclic
    {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z]
    {a b : Z} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have ha1 : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; norm_num at ha
  have hb1 : b ≠ 1 := by intro h; rw [h, orderOf_one] at hb; norm_num at hb
  exact CFSG.GH74.GLS.Bg.L1621.cyclic_invol_unique ha2 hb2 ha1 hb1


theorem centralProduct_square (l : ℕ) (c : Multiplicative (ZMod (4 * l)))
    (q : QuaternionGroup 2) (hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2) :
    (centralProductProjection l (c, q)) ^ 2 =
      element (4 * l) (2 • Multiplicative.toAdd c + (2 * l : ℕ))
        (2 • Multiplicative.toAdd c + (2 * l : ℕ)) 0 := by
  rw [← map_pow]
  change centralProductProjection l (c ^ 2, q ^ 2) = _
  rw [quaternionEight_noncentral_square q hq]
  change element (4 * l) (2 • Multiplicative.toAdd c) (2 • Multiplicative.toAdd c) 0 *
    element (4 * l) (quarterScale l 2) (-quarterScale l 2) 0 = _
  rw [quarterScale_two, element_base_mul]
  have hneg : -((2 * l : ℕ) : ZMod (4 * l)) = (2 * l : ℕ) := by
    linear_combination -(twice_quarter_add_self l)
  rw [hneg]

theorem centralProduct_central_of_central_quaternion (l : ℕ) (hl : 0 < l)
    (c : Multiplicative (ZMod (4 * l))) (q : QuaternionGroup 2)
    (hq : q = 1 ∨ q = QuaternionGroup.a 2) :
    centralProductProjection l (c, q) ∈ Subgroup.center (Wreath (4 * l)) := by
  rw [centralProductProjection, MonoidHom.noncommCoprod_apply]
  apply (Subgroup.center (Wreath (4 * l))).mul_mem
  · exact (element_mem_center_iff _ (by omega) _ _ _).mpr ⟨rfl, rfl⟩
  · exact (quaternionEight_mem_center_iff l hl q).mpr hq

theorem v_noncentral_order_four_iff (l : ℕ) (hl : 0 < l) (g : Wreath (4 * l))
    (hg : g ∈ vSubgroup l) (hn : g ∉ Subgroup.center (Wreath (4 * l))) :
    orderOf g = 4 ↔ g ∈ quaternionEightSubgroup l := by
  constructor
  · intro horder
    have himg : g ∈ (centralProductProjection l).range :=
      (centralProductProjection_range l hl).symm ▸ hg
    obtain ⟨⟨c, q⟩, rfl⟩ := himg
    have hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2 := by
      constructor <;> intro heq
      · exact hn (centralProduct_central_of_central_quaternion l hl c q (Or.inl heq))
      · exact hn (centralProduct_central_of_central_quaternion l hl c q (Or.inr heq))
    have hs := centralProduct_square l c q hq
    have hfour : (centralProductProjection l (c, q)) ^ 4 = 1 := by
      simpa only [horder] using pow_orderOf_eq_one (centralProductProjection l (c, q))
    have htwo : (centralProductProjection l (c, q)) ^ 2 ≠ 1 := by
      intro ht
      have hd := orderOf_dvd_of_pow_eq_one ht
      rw [horder] at hd
      norm_num at hd
    have hfour' : ((centralProductProjection l (c, q)) ^ 2) ^ 2 = 1 := by
      simpa only [← pow_mul] using hfour
    rw [hs, element_base_pow, element_base_eq_one_iff] at hfour'
    have hkill : 2 • (2 • Multiplicative.toAdd c) = 0 := by
      have hh := hfour'.1
      rw [smul_add, two_nsmul ((2 * l : ℕ) : ZMod (4 * l)), twice_quarter_add_self l,
        add_zero] at hh
      exact hh
    have hc : 2 • Multiplicative.toAdd c = 0 := by
      rcases (two_smul_eq_zero_half_quarter l hl _).mp hkill with hh | hh
      · exact hh
      · apply False.elim
        apply htwo
        rw [hs, hh, twice_quarter_add_self l, element_zero]
    rcases (two_smul_eq_zero_half_quarter l hl _).mp hc with hc | hc
    · rw [centralProductProjection, MonoidHom.noncommCoprod_apply]
      have hd : diagonalHom (4 * l) c = 1 := by
        change element (4 * l) (Multiplicative.toAdd c) (Multiplicative.toAdd c) 0 = 1
        rw [hc, element_zero]
      rw [hd, one_mul]
      exact ⟨q, rfl⟩
    · rw [centralProductProjection, MonoidHom.noncommCoprod_apply]
      apply (quaternionEightSubgroup l).mul_mem
      · refine ⟨QuaternionGroup.a 2, ?_⟩
        change element (4 * l) (quarterScale l 2) (-quarterScale l 2) 0 =
          element (4 * l) (Multiplicative.toAdd c) (Multiplicative.toAdd c) 0
        rw [hc, quarterScale_two]
        have hneg : -((2 * l : ℕ) : ZMod (4 * l)) = (2 * l : ℕ) := by
          linear_combination -(twice_quarter_add_self l)
        rw [hneg]
      · exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    have hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2 := by
      have hn' := mt (quaternionEight_mem_center_iff l hl q).mpr hn
      simpa only [not_or] using hn'
    rw [orderOf_injective _ (quaternionEightEmbedding_injective l hl)]
    exact quaternionEight_noncentral_order q hq

theorem v_center_map (l : ℕ) (hl : 0 < l) :
    (Subgroup.center (vSubgroup l)).map (vSubgroup l).subtype =
      Subgroup.center (Wreath (4 * l)) := by
  rw [nonabelian_subgroup_center _ (by omega) _ (v_is_nonabelian l hl),
    inf_eq_right.mpr (center_le_v l hl)]

theorem v_mem_center_iff (l : ℕ) (hl : 0 < l) (g : vSubgroup l) :
    g ∈ Subgroup.center (vSubgroup l) ↔ g.val ∈ Subgroup.center (Wreath (4 * l)) := by
  constructor
  · intro hg
    rw [← v_center_map l hl]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hg a.val

@[expose] def quaternionInV (l : ℕ) : Subgroup (vSubgroup l) :=
  (quaternionEightSubgroup l).subgroupOf (vSubgroup l)

theorem quaternionInV_noncentral_iff (l : ℕ) (hl : 0 < l) (g : vSubgroup l)
    (hn : g ∉ Subgroup.center (vSubgroup l)) :
    g ∈ quaternionInV l ↔ orderOf g = 4 := by
  have hn' : g.val ∉ Subgroup.center (Wreath (4 * l)) :=
    mt (v_mem_center_iff l hl g).mpr hn
  change g.val ∈ quaternionEightSubgroup l ↔ orderOf g = 4
  rw [← v_noncentral_order_four_iff l hl g.val g.property hn']
  have ho : orderOf g.val = orderOf g :=
    orderOf_injective (vSubgroup l).subtype Subtype.val_injective g
  rw [ho]

@[expose] def quaternionToV (l : ℕ) : QuaternionGroup 2 →* vSubgroup l :=
  (quaternionEightEmbedding l).codRestrict (vSubgroup l) (fun q =>
    quaternionEight_le_v l ⟨q, rfl⟩)

theorem quaternionToV_injective (l : ℕ) (hl : 0 < l) :
    Function.Injective (quaternionToV l) := by
  intro q r h
  exact quaternionEightEmbedding_injective l hl (congrArg Subtype.val h)

theorem quaternionToV_range (l : ℕ) : (quaternionToV l).range = quaternionInV l := by
  ext g
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, Subtype.ext hq⟩

theorem quaternionToV_noncentral (l : ℕ) (hl : 0 < l) (q : QuaternionGroup 2)
    (hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2) :
    quaternionToV l q ∉ Subgroup.center (vSubgroup l) := by
  rw [v_mem_center_iff l hl]
  change quaternionEightEmbedding l q ∉ Subgroup.center (Wreath (4 * l))
  rw [quaternionEight_mem_center_iff l hl]
  exact not_or.mpr hq

theorem quaternionInV_eq_intrinsic_closure (l : ℕ) (hl : 0 < l) :
    quaternionInV l = Subgroup.closure
      {g : vSubgroup l | g ∉ Subgroup.center (vSubgroup l) ∧ orderOf g = 4} := by
  let H := Subgroup.closure
    {g : vSubgroup l | g ∉ Subgroup.center (vSubgroup l) ∧ orderOf g = 4}
  have hgen (q : QuaternionGroup 2) (hq : q ≠ 1 ∧ q ≠ QuaternionGroup.a 2) :
      quaternionToV l q ∈ H := by
    apply Subgroup.subset_closure
    refine ⟨quaternionToV_noncentral l hl q hq, ?_⟩
    rw [orderOf_injective _ (quaternionToV_injective l hl)]
    exact quaternionEight_noncentral_order q hq
  have hr : quaternionToV l (QuaternionGroup.a 1) ∈ H := hgen _ (by decide)
  have hd : quaternionToV l (QuaternionGroup.xa 0) ∈ H := hgen _ (by decide)
  apply le_antisymm
  · intro g hg
    rw [← quaternionToV_range] at hg
    obtain ⟨q, rfl⟩ := hg
    have hrot (i : ZMod 4) : quaternionToV l (QuaternionGroup.a i) ∈ H := by
      have hp := H.pow_mem hr i.val
      rw [← map_pow, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val] at hp
      exact hp
    cases q with
    | a i => exact hrot i
    | xa i =>
      have hp := H.mul_mem hd (hrot i)
      rw [← map_mul, QuaternionGroup.xa_mul_a, zero_add] at hp
      exact hp
  · rw [Subgroup.closure_le]
    intro g hg
    exact (quaternionInV_noncentral_iff l hl g hg.1).mpr hg.2

theorem quaternionInV_characteristic (l : ℕ) (hl : 0 < l) :
    (quaternionInV l).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [quaternionInV_eq_intrinsic_closure l hl, MonoidHom.map_closure, Subgroup.closure_le]
  rintro g ⟨a, ha, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · intro hφ
    have hcenter : (Subgroup.center (vSubgroup l)).comap φ.toMonoidHom =
        Subgroup.center (vSubgroup l) :=
      Subgroup.Characteristic.fixed inferInstance φ
    have hmem : a ∈ (Subgroup.center (vSubgroup l)).comap φ.toMonoidHom := hφ
    rw [hcenter] at hmem
    exact ha.1 hmem
  · change orderOf (φ a) = 4
    rw [φ.orderOf_eq, ha.2]

theorem quaternionInV_noncentral_set (l : ℕ) (hl : 0 < l) :
    {g : vSubgroup l | g ∉ Subgroup.center (vSubgroup l) ∧ orderOf g = 4} =
      quaternionToV l '' {q : QuaternionGroup 2 | q ≠ 1 ∧ q ≠ QuaternionGroup.a 2} := by
  ext g
  constructor
  · intro hg
    have hq := (quaternionInV_noncentral_iff l hl g hg.1).mpr hg.2
    rw [← quaternionToV_range] at hq
    obtain ⟨q, rfl⟩ := hq
    refine ⟨q, ?_, rfl⟩
    have hn : quaternionEightEmbedding l q ∉ Subgroup.center (Wreath (4 * l)) :=
      mt (v_mem_center_iff l hl (quaternionToV l q)).mpr hg.1
    change q ≠ 1 ∧ q ≠ QuaternionGroup.a 2
    simpa only [quaternionEight_mem_center_iff l hl, not_or] using hn
  · rintro ⟨q, hq, rfl⟩
    refine ⟨quaternionToV_noncentral l hl q hq, ?_⟩
    rw [orderOf_injective _ (quaternionToV_injective l hl)]
    exact quaternionEight_noncentral_order q hq

theorem card_v_noncentral_order_four (l : ℕ) (hl : 0 < l) :
    Nat.card {g : vSubgroup l | g ∉ Subgroup.center (vSubgroup l) ∧ orderOf g = 4} = 6 := by
  rw [quaternionInV_noncentral_set l hl,
    Nat.card_image_of_injective (quaternionToV_injective l hl)]
  rw [Nat.card_eq_fintype_card]
  decide

end CFSG.Wreathed
