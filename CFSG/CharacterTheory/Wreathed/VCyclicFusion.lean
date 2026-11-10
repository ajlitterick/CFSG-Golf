module

public import CFSG.CharacterTheory.Wreathed.CentricVCopies
public import CFSG.CharacterTheory.Wreathed.SubgroupDihedralQuotient
public import CFSG.GroupTheory.KleinFourAutomorphism
public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u v


@[expose] def subgroupCenterProjection {A : Type u} [Group A]
    (H K : Subgroup A) (hHK : H ≤ K) : H →* K ⧸ Subgroup.center K :=
  (QuotientGroup.mk' (Subgroup.center K)).comp (Subgroup.inclusion hHK)

theorem original_quaternion_le_v (n : ℕ) (hn : 2 ≤ n) :
    Original.Q (2 ^ n) ≤ Original.V (2 ^ n) := by
  rw [(wreath_center_involution_and_quaternion_coordinates n hn).central_product]
  exact le_sup_right

@[expose] def originalQuaternionCenterProjection (n : ℕ) (hn : 2 ≤ n) :
    Original.Q (2 ^ n) →* Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n)) :=
  subgroupCenterProjection _ _ (original_quaternion_le_v n hn)

theorem original_quaternion_projection_cover (n : ℕ) (hn : 2 ≤ n) :
    ∃ e : QuaternionGroup 2 ≃* Original.Q (2 ^ n),
      (∀ q : QuaternionGroup 2, originalQuaternionCenterProjection n hn (e q) = 1 ↔
        q = 1 ∨ q = QuaternionGroup.a 2) ∧
      Function.Surjective (originalQuaternionCenterProjection n hn) := by
  have hm : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    ring
  unfold originalQuaternionCenterProjection
  generalize original_quaternion_le_v n hn = hle
  revert hle
  rw [hm, Original.Q_atQuarter, Original.V_atQuarter]
  intro hle
  let l := 2 ^ (n - 2)
  have hl : 0 < l := pow_pos (by decide) _
  refine ⟨quaternionEightRangeEquiv l hl, ?_, ?_⟩
  · intro q
    change vQuotientQuaternionProjection l q = 1 ↔ _
    exact vQuotientQuaternionProjection_eq_one_iff l hl q
  · intro x
    obtain ⟨q, rfl⟩ := vQuotientQuaternionProjection_surjective l hl x
    exact ⟨quaternionEightRangeEquiv l hl q, rfl⟩

@[expose] def originalQuaternionProjectionEquiv (n : ℕ) (hn : 2 ≤ n) :
    QuaternionGroup 2 ≃* Original.Q (2 ^ n) :=
  (original_quaternion_projection_cover n hn).choose

theorem originalQuaternionCenterProjection_kernel (n : ℕ) (hn : 2 ≤ n)
    (q : QuaternionGroup 2) :
    originalQuaternionCenterProjection n hn (originalQuaternionProjectionEquiv n hn q) = 1 ↔
      q = 1 ∨ q = QuaternionGroup.a 2 :=
  (original_quaternion_projection_cover n hn).choose_spec.1 q

theorem originalQuaternionCenterProjection_surjective (n : ℕ) (hn : 2 ≤ n) :
    Function.Surjective (originalQuaternionCenterProjection n hn) :=
  (original_quaternion_projection_cover n hn).choose_spec.2


theorem original_v_quotient_card_four (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) = 4 := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  have hcard := (Subgroup.center (Original.V (2 ^ n))).card_eq_card_quotient_mul_card_subgroup
  rw [hstructure.central_product_card, original_v_center_card n hn] at hcard
  nlinarith [pow_pos (by decide : 0 < (2 : ℕ)) n]

theorem original_v_quotient_isKleinFour (n : ℕ) (hn : 2 ≤ n) :
    IsKleinFour (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  have hcenter : Subgroup.center (Wreath (2 ^ n)) ≤ Original.V (2 ^ n) := by
    rw [hstructure.center, hstructure.central_product]
    exact le_sup_left
  obtain ⟨k, hk, _, ⟨e⟩, hcard⟩ := nonabelian_subgroup_center_quotient_dihedral_card hn
    (Original.V (2 ^ n)) (original_v_is_nonabelian n hn) hcenter
  have hkone : k = 1 := by
    by_contra hne
    have hpow : 8 ≤ 2 ^ (k + 1) := by
      calc
        8 = 2 ^ 3 := by decide
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hstructure.central_product_card] at hcard
    nlinarith [pow_pos (by decide : 0 < (2 : ℕ)) n]
  subst k
  refine ⟨original_v_quotient_card_four n hn, ?_⟩
  rw [Monoid.exponent_eq_of_mulEquiv e]
  exact IsKleinFour.exponent_two (G := DihedralGroup 2)


theorem quaternionInsideOriginalV_characteristic (n : ℕ) (hn : 2 ≤ n) :
    ((Original.Q (2 ^ n)).subgroupOf (Original.V (2 ^ n))).Characteristic :=
  (wreath_center_involution_and_quaternion_coordinates n hn).quaternion_characteristic

@[expose] def originalQuaternionInclusionEquiv (n : ℕ) (hn : 2 ≤ n) :
    Original.Q (2 ^ n) ≃*
      (Original.Q (2 ^ n)).subgroupOf (Original.V (2 ^ n)) :=
  (Subgroup.subgroupOfEquivOfLe (original_quaternion_le_v n hn)).symm

@[expose] def originalQuaternionAutomorphism (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n))) : MulAut (Original.Q (2 ^ n)) :=
  letI := quaternionInsideOriginalV_characteristic n hn
  MulAut.congr (originalQuaternionInclusionEquiv n hn).symm
    (CFSG.FiveTransitive.CharacteristicAutomorphism.restrict
      ((Original.Q (2 ^ n)).subgroupOf (Original.V (2 ^ n))) a)

theorem originalQuaternionAutomorphism_coe (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n))) (g : Original.Q (2 ^ n)) :
    (originalQuaternionAutomorphism n hn a g).val =
      (a (Subgroup.inclusion (original_quaternion_le_v n hn) g)).val := by
  rfl

@[expose] def originalVQuotientAutomorphism (n : ℕ)
    (a : MulAut (Original.V (2 ^ n))) :
    MulAut (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) :=
  CFSG.FiveTransitive.CharacteristicAutomorphism.quotient
    (Subgroup.center (Original.V (2 ^ n))) a

theorem originalVQuotientAutomorphism_mk (n : ℕ)
    (a : MulAut (Original.V (2 ^ n))) (g : Original.V (2 ^ n)) :
    originalVQuotientAutomorphism n a
      ((QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) g) =
        (QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) (a g) :=
  CFSG.FiveTransitive.CharacteristicAutomorphism.quotient_apply_mk _ a g

theorem originalVQuotientAutomorphism_pow (n : ℕ)
    (a : MulAut (Original.V (2 ^ n))) (i : ℕ) :
    originalVQuotientAutomorphism n (a ^ i) = originalVQuotientAutomorphism n a ^ i :=
  map_pow (CFSG.FiveTransitive.CharacteristicAutomorphism.quotient
    (Subgroup.center (Original.V (2 ^ n)))) a i


theorem originalQuaternionCenterProjection_intertwines (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n))) (g : Original.Q (2 ^ n)) :
    originalQuaternionCenterProjection n hn (originalQuaternionAutomorphism n hn a g) =
      originalVQuotientAutomorphism n a (originalQuaternionCenterProjection n hn g) := by
  change (QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n))))
    (Subgroup.inclusion (original_quaternion_le_v n hn)
      (originalQuaternionAutomorphism n hn a g)) = _
  rw [show Subgroup.inclusion (original_quaternion_le_v n hn)
      (originalQuaternionAutomorphism n hn a g) =
      a (Subgroup.inclusion (original_quaternion_le_v n hn) g) from
        Subtype.ext (originalQuaternionAutomorphism_coe n hn a g)]
  exact (originalVQuotientAutomorphism_mk n a _).symm


theorem originalVQuotientAutomorphism_cycles_three (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n)))
    (horder : orderOf (originalVQuotientAutomorphism n a) = 3)
    (x : Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) (hx : x ≠ 1) :
    originalVQuotientAutomorphism n a x ≠ x ∧
      originalVQuotientAutomorphism n a (originalVQuotientAutomorphism n a x) ≠ x ∧
      originalVQuotientAutomorphism n a (originalVQuotientAutomorphism n a x) ≠
        originalVQuotientAutomorphism n a x ∧
      ∀ y : Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n)),
        y ≠ 1 → y = x ∨ y = originalVQuotientAutomorphism n a x ∨
          y = originalVQuotientAutomorphism n a (originalVQuotientAutomorphism n a x) := by
  let := original_v_quotient_isKleinFour n hn
  exact CFSG.kleinFour_order_three_cycle _ (originalVQuotientAutomorphism n a) horder x hx


@[expose] def originalVSwap (m : ℕ) : Original.V m :=
  ⟨Original.z m, Subgroup.subset_closure (by simp)⟩

@[expose] def originalVHalf (m : ℕ) : Original.V m :=
  ⟨Original.x2 m, Subgroup.subset_closure (by simp)⟩

@[expose] def originalVSwapCoset (m : ℕ) : Original.V m ⧸ Subgroup.center (Original.V m) :=
  (QuotientGroup.mk' (Subgroup.center (Original.V m))) (originalVSwap m)

@[expose] def originalVHalfCoset (m : ℕ) : Original.V m ⧸ Subgroup.center (Original.V m) :=
  (QuotientGroup.mk' (Subgroup.center (Original.V m))) (originalVHalf m)


theorem original_swap_half_cosets_distinct (n : ℕ) (hn : 2 ≤ n) :
    originalVSwapCoset (2 ^ n) ≠ 1 ∧ originalVHalfCoset (2 ^ n) ≠ 1 ∧
      originalVSwapCoset (2 ^ n) ≠ originalVHalfCoset (2 ^ n) := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  have hm : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  have hcentral (g : Original.V (2 ^ n))
      (hg : g ∈ Subgroup.center (Original.V (2 ^ n))) :
      g.val ∈ Subgroup.center (Wreath (2 ^ n)) := by
    rw [hstructure.center, ← hstructure.central_product_center]
    exact ⟨g, hg, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hc := hcentral _ ((QuotientGroup.eq_one_iff _).mp h)
    change element (2 ^ n) 0 0 1 ∈ Subgroup.center (Wreath (2 ^ n)) at hc
    exact one_ne_zero ((element_mem_center_iff _ hm _ _ _).mp hc).1
  · intro h
    have hc := hcentral _ ((QuotientGroup.eq_one_iff _).mp h)
    change Original.x2 (2 ^ n) ∈ Subgroup.center (Wreath (2 ^ n)) at hc
    rw [Original.x2_eq, element_mem_center_iff _ hm] at hc
    have hx : Original.x2 (2 ^ n) = 1 := by rw [Original.x2_eq, hc.2, element_zero]
    have ho := hstructure.involution_orders.2.1
    rw [hx, orderOf_one] at ho
    omega
  · intro h
    have hc := hcentral _ (QuotientGroup.eq_iff_div_mem.mp h)
    change Original.z (2 ^ n) * (Original.x2 (2 ^ n))⁻¹ ∈
      Subgroup.center (Wreath (2 ^ n)) at hc
    rw [Original.z, Original.x2_eq, element_base_inv, element_swap_mul, add_zero,
      zero_add, element_mem_center_iff _ hm] at hc
    exact one_ne_zero hc.1

theorem vCyclic_twice_half_height (n : ℕ) (hn : 1 ≤ n) :
    (((2 ^ n / 2 : ℕ) : ZMod (2 ^ n))) + (2 ^ n / 2 : ℕ) = 0 := by
  have hhalf : 2 ^ n / 2 + 2 ^ n / 2 = 2 ^ n := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ, Nat.mul_div_cancel _ (by decide : 0 < (2 : ℕ))]
    omega
  rw [← Nat.cast_add, hhalf, ZMod.natCast_self]

theorem vCyclic_two_smul_eq_zero_height (n : ℕ) (hn : 1 ≤ n) (c : ZMod (2 ^ n)) :
    2 • c = 0 ↔ c = 0 ∨ c = (2 ^ n / 2 : ℕ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hhalf : 2 ^ (k + 1) / 2 = 2 ^ k := by
    rw [pow_succ, Nat.mul_div_cancel _ (by decide : 0 < (2 : ℕ))]
  rw [hhalf]
  exact two_smul_eq_zero_iff k c

theorem original_involution_in_half_coset (n : ℕ) (hn : 2 ≤ n)
    (g : Original.V (2 ^ n)) (horder : orderOf g = 2)
    (hcoset : (QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) g =
      originalVHalfCoset (2 ^ n)) :
    g.val = Original.x2 (2 ^ n) ∨
      g.val = Original.t (2 ^ n) ^ (2 ^ n / 2) := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  have hm : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  have hc : (g / originalVHalf (2 ^ n)).val ∈ Subgroup.center (Wreath (2 ^ n)) := by
    rw [hstructure.center, ← hstructure.central_product_center]
    exact ⟨g / originalVHalf (2 ^ n), QuotientGroup.eq_iff_div_mem.mp hcoset, rfl⟩
  obtain ⟨⟨a, b, e⟩, hcoord⟩ :=
    (coordinateEquiv (2 ^ n)).symm.surjective (g / originalVHalf (2 ^ n)).val
  change element (2 ^ n) a b e = (g / originalVHalf (2 ^ n)).val at hcoord
  rw [← hcoord, element_mem_center_iff _ hm] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have hform : g.val = element (2 ^ n) (a + (2 ^ n / 2 : ℕ)) a 0 := by
    calc
      g.val = (g / originalVHalf (2 ^ n)).val * (originalVHalf (2 ^ n)).val := by
        change g.val = (g.val / (originalVHalf (2 ^ n)).val) * (originalVHalf (2 ^ n)).val
        exact (div_mul_cancel _ _).symm
      _ = element (2 ^ n) a a 0 * Original.x2 (2 ^ n) := by rw [← hcoord]; rfl
      _ = element (2 ^ n) (a + (2 ^ n / 2 : ℕ)) a 0 := by
        rw [Original.x2_eq, element_base_mul, add_zero]
  have hsquare : g.val ^ 2 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [horder] at h
    exact congrArg Subtype.val h
  rw [hform, element_base_pow, element_base_eq_one_iff] at hsquare
  rcases (vCyclic_two_smul_eq_zero_height n (by omega) a).mp hsquare.2 with rfl | rfl
  · exact Or.inl (by simpa only [zero_add, Original.x2_eq] using hform)
  · exact Or.inr (by simpa only [vCyclic_twice_half_height n (by omega), Original.t,
      element_base_pow, nsmul_eq_mul, mul_zero, mul_one] using hform)

theorem originalVSwap_order (m : ℕ) : orderOf (originalVSwap m) = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact Original.orderOf_z m

theorem originalVAutomorphism_swap_half_endpoint (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n)))
    (hcoset : originalVQuotientAutomorphism n a (originalVSwapCoset (2 ^ n)) =
      originalVHalfCoset (2 ^ n)) :
    (a (originalVSwap (2 ^ n))).val = Original.x2 (2 ^ n) ∨
      (a (originalVSwap (2 ^ n))).val = Original.t (2 ^ n) ^ (2 ^ n / 2) := by
  apply original_involution_in_half_coset n hn
  · exact (a.orderOf_eq _).trans (originalVSwap_order _)
  · exact (originalVQuotientAutomorphism_mk n a _).symm.trans hcoset

theorem originalVQuotientAutomorphism_swap_reaches_half (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n)))
    (horder : orderOf (originalVQuotientAutomorphism n a) = 3) :
    ∃ i : ℕ, (i = 1 ∨ i = 2) ∧
      (originalVQuotientAutomorphism n a ^ i) (originalVSwapCoset (2 ^ n)) =
        originalVHalfCoset (2 ^ n) := by
  obtain ⟨hswap, hhalf, hdistinct⟩ := original_swap_half_cosets_distinct n hn
  obtain ⟨_, _, _, hcover⟩ := originalVQuotientAutomorphism_cycles_three n hn a horder
    (originalVSwapCoset (2 ^ n)) hswap
  rcases hcover (originalVHalfCoset (2 ^ n)) hhalf with h | h | h
  · exact False.elim (hdistinct h.symm)
  · exact ⟨1, Or.inl rfl, by simpa only [pow_one] using h.symm⟩
  · exact ⟨2, Or.inr rfl, by simpa only [pow_two, MulAut.mul_apply] using h.symm⟩

theorem originalVAutomorphism_order_three_swap_endpoint (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n)))
    (horder : orderOf (originalVQuotientAutomorphism n a) = 3) :
    ∃ i : ℕ, (i = 1 ∨ i = 2) ∧
      (((a ^ i) (originalVSwap (2 ^ n))).val = Original.x2 (2 ^ n) ∨
        ((a ^ i) (originalVSwap (2 ^ n))).val = Original.t (2 ^ n) ^ (2 ^ n / 2)) := by
  obtain ⟨i, hi, hcoset⟩ := originalVQuotientAutomorphism_swap_reaches_half n hn a horder
  refine ⟨i, hi, originalVAutomorphism_swap_half_endpoint n hn (a ^ i) ?_⟩
  rwa [originalVQuotientAutomorphism_pow]

end CFSG.Wreathed
