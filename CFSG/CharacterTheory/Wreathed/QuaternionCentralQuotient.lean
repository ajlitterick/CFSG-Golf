module

public import CFSG.CharacterTheory.Wreathed.CentralizerFusion
public import CFSG.CharacterTheory.Semidihedral.CentralQuotients

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u

namespace Original

theorem Y_even (h : ℕ) : Y (2 * h) = quaternionSubgroup h := by
  rw [Y, r_eq, d_eq, show 2 * h / 2 = h by omega]
  exact (quaternion_range_eq_generated h).symm

theorem Y_map_modulus {m k : ℕ} (h : m = k) :
    (Y m).map (modulusEquiv h).toMonoidHom = Y k := by
  subst k
  simp [modulusEquiv]

end Original

@[expose] def originalYEvenEquiv (h : ℕ) :
    QuaternionGroup h ≃* Original.Y (2 * h) :=
  (quaternionRangeEquiv h).trans (MulEquiv.subgroupCongr (Original.Y_even h).symm)

theorem originalYEvenEquiv_coe_a (h : ℕ) (i : ZMod (2 * h)) :
    (originalYEvenEquiv h (QuaternionGroup.a i) : Wreath (2 * h)) =
      element (2 * h) i (-i) 0 := rfl


theorem originalYEvenEquiv_involution (h : ℕ) :
    (originalYEvenEquiv h (QuaternionGroup.a (h : ZMod (2 * h))) : Wreath (2 * h)) =
      Original.x (2 * h) := by
  rw [originalYEvenEquiv_coe_a, Original.x_eq, half_modulus_neg,
    show 2 * h / 2 = h by omega]

theorem wreath_modulus_twice_half (n : ℕ) (hn : 1 ≤ n) :
    2 * (2 ^ n / 2) = 2 ^ n := by
  have hdiv : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
  exact Nat.mul_div_cancel' hdiv

@[expose] def originalYQuaternionEquiv (n : ℕ) (hn : 2 ≤ n) :
    QuaternionGroup (2 ^ n / 2) ≃* Original.Y (2 ^ n) :=
  (originalYEvenEquiv (2 ^ n / 2)).trans
    (((modulusEquiv (wreath_modulus_twice_half n (by omega))).subgroupMap
      (Original.Y (2 * (2 ^ n / 2)))).trans
      (MulEquiv.subgroupCongr (Original.Y_map_modulus
        (wreath_modulus_twice_half n (by omega)))))

theorem two_nsmul_eq_zero_twice_modulus (h : ℕ) (hh : 0 < h) (i : ZMod (2 * h)) :
    2 • i = 0 ↔ i = 0 ∨ i = (h : ℕ) := by
  let : NeZero (2 * h) := ⟨by omega⟩
  have hlt := ZMod.val_lt i
  have heq : 2 • i = ((2 * i.val : ℕ) : ZMod (2 * h)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]
  rw [heq, ZMod.natCast_eq_zero_iff,
    Nat.mul_dvd_mul_iff_left (by decide : 0 < (2 : ℕ))]
  constructor
  · rintro ⟨k, hk⟩
    have hklt : k < 2 := by nlinarith
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · left
      have hz : i.val = 0 := by simpa using hk
      rw [← ZMod.natCast_zmod_val i, hz, Nat.cast_zero]
    · right
      have hz : i.val = h := by simpa using hk
      rw [← ZMod.natCast_zmod_val i, hz]
  · rintro (rfl | rfl)
    · simp
    · rw [ZMod.val_natCast_of_lt (by omega)]

theorem nativeQuaternion_unique_involution (h : ℕ) (hh : 0 < h)
    (q : QuaternionGroup h) (hq : orderOf q = 2) :
    q = QuaternionGroup.a (h : ZMod (2 * h)) := by
  let : NeZero h := ⟨by omega⟩
  cases q with
  | a i =>
    have hs : 2 • i = 0 := by
      have hpow : (QuaternionGroup.a i : QuaternionGroup h) ^ 2 = 1 := by
        simpa only [hq] using pow_orderOf_eq_one (QuaternionGroup.a i : QuaternionGroup h)
      rw [pow_two, QuaternionGroup.a_mul_a] at hpow
      have hsum : i + i = 0 := QuaternionGroup.a.inj hpow
      simpa only [two_nsmul] using hsum
    rcases (two_nsmul_eq_zero_twice_modulus h hh i).mp hs with rfl | rfl
    · have hone : (QuaternionGroup.a 0 : QuaternionGroup h) = 1 := rfl
      rw [hone, orderOf_one] at hq
      omega
    · rfl
  | xa i =>
    rw [QuaternionGroup.orderOf_xa] at hq
    omega

theorem nativeQuaternion_center_eq (h : ℕ) (hh : 1 < h) :
    Subgroup.center (QuaternionGroup h) = CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ h := by
  let : NeZero h := ⟨by omega⟩
  apply le_antisymm
  · intro q hq
    cases q with
    | a i =>
      have hc := Subgroup.mem_center_iff.mp hq (QuaternionGroup.xa 0)
      rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa, zero_add, zero_sub] at hc
      have hi : i = -i := QuaternionGroup.xa.inj hc
      have hs : 2 • i = 0 := by
        rw [two_nsmul]
        calc i + i = i + -i := congrArg (i + ·) hi
             _ = 0 := add_neg_cancel i
      rcases (two_nsmul_eq_zero_twice_modulus h (by omega) i).mp hs with rfl | rfl
      · exact (CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ h).one_mem
      · exact Subgroup.mem_zpowers _
    | xa i =>
      have hc := Subgroup.mem_center_iff.mp hq (QuaternionGroup.a 1)
      rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hc
      have hi : i - 1 = i + 1 := QuaternionGroup.xa.inj hc
      have htwo : (2 : ZMod (2 * h)) = 0 := by linear_combination -hi
      have hdiv : 2 * h ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 * h)).mp htwo
      have hle : 2 * h ≤ 2 := Nat.le_of_dvd (by decide) hdiv
      omega
  · exact Subgroup.zpowers_le.mpr (CFSG.Semidihedral.CentralQuotients.nativeQuaternion_half_mem_center h)


theorem modulusEquiv_original_x {m k : ℕ} (h : m = k) :
    modulusEquiv h (Original.x m) = Original.x k := by
  subst k
  rfl


theorem originalYQuaternionEquiv_involution (n : ℕ) (hn : 2 ≤ n) :
    (originalYQuaternionEquiv n hn
      (QuaternionGroup.a ((2 ^ n / 2 : ℕ) : ZMod (2 * (2 ^ n / 2)))) : Wreath (2 ^ n)) =
      Original.x (2 ^ n) := by
  change modulusEquiv (wreath_modulus_twice_half n (by omega))
    (originalYEvenEquiv (2 ^ n / 2)
      (QuaternionGroup.a ((2 ^ n / 2 : ℕ) : ZMod (2 * (2 ^ n / 2)))) :
        Wreath (2 * (2 ^ n / 2))) = _
  rw [originalYEvenEquiv_involution, modulusEquiv_original_x]

theorem original_x_mem_Y (n : ℕ) (hn : 2 ≤ n) :
    Original.x (2 ^ n) ∈ Original.Y (2 ^ n) :=
  (originalYQuaternionEquiv_involution n hn) ▸
    (originalYQuaternionEquiv n hn (QuaternionGroup.a ((2 ^ n / 2 : ℕ) :
      ZMod (2 * (2 ^ n / 2))))).property

@[expose] def originalYInvolution (n : ℕ) (hn : 2 ≤ n) : Original.Y (2 ^ n) :=
  ⟨Original.x (2 ^ n), original_x_mem_Y n hn⟩


theorem originalY_unique_involution (n : ℕ) (hn : 2 ≤ n)
    (y : Original.Y (2 ^ n)) (hy : orderOf y = 2) : y = originalYInvolution n hn := by
  have hh : 0 < 2 ^ n / 2 := by
    have hpow : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega : 1 ≤ n)
    omega
  obtain ⟨q, rfl⟩ := (originalYQuaternionEquiv n hn).surjective y
  have hq : orderOf q = 2 := ((originalYQuaternionEquiv n hn).orderOf_eq q).symm.trans hy
  rw [nativeQuaternion_unique_involution _ hh q hq]
  apply Subtype.ext
  exact originalYQuaternionEquiv_involution n hn

theorem originalY_center_eq_zpowers (n : ℕ) (hn : 2 ≤ n) :
    Subgroup.center (Original.Y (2 ^ n)) = Subgroup.zpowers (originalYInvolution n hn) := by
  have hh : 1 < 2 ^ n / 2 := by
    have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  rw [← Subgroup.map_center_eq (originalYQuaternionEquiv n hn), nativeQuaternion_center_eq _ hh,
    CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ, MonoidHom.map_zpowers]
  congr 1
  exact Subtype.ext (originalYQuaternionEquiv_involution n hn)


theorem originalY_center_map (n : ℕ) (hn : 2 ≤ n) :
    (Subgroup.center (Original.Y (2 ^ n))).map (Original.Y (2 ^ n)).subtype =
      Subgroup.zpowers (Original.x (2 ^ n)) := by
  rw [originalY_center_eq_zpowers n hn, MonoidHom.map_zpowers]
  rfl

theorem originalY_is_nonabelian (n : ℕ) (hn : 2 ≤ n) :
    ∃ a b : Original.Y (2 ^ n), a * b ≠ b * a := by
  let E := originalYQuaternionEquiv n hn
  refine ⟨E (QuaternionGroup.a 1), E (QuaternionGroup.xa 0), ?_⟩
  intro heq
  have hsource : (QuaternionGroup.a 1 : QuaternionGroup (2 ^ n / 2)) * QuaternionGroup.xa 0 =
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
    apply E.injective
    simpa only [map_mul] using heq
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, zero_sub, zero_add] at hsource
  have hsum : (2 : ZMod (2 * (2 ^ n / 2))) = 0 := by
    have hi : -(1 : ZMod (2 * (2 ^ n / 2))) = 1 := QuaternionGroup.xa.inj hsource
    linear_combination -hi
  have hdiv : 2 * (2 ^ n / 2) ∣ 2 :=
    (ZMod.natCast_eq_zero_iff 2 (2 * (2 ^ n / 2))).mp hsum
  rw [wreath_modulus_twice_half n (by omega)] at hdiv
  have hle : 2 ^ n ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  have hge : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  omega

theorem original_Z_inf_Y (n : ℕ) (hn : 2 ≤ n) :
    Original.Z (2 ^ n) ⊓ Original.Y (2 ^ n) = Subgroup.zpowers (Original.x (2 ^ n)) := by
  have hcenter := (wreath_center_involution_and_quaternion_coordinates n hn).nonabelian_centralizers
    (Original.Y (2 ^ n)) (originalY_is_nonabelian n hn)
  exact (inf_comm _ _).trans (hcenter.2.symm.trans (originalY_center_map n hn))

variable {G : Type u} [Group G]

@[expose] def modelYEquiv {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Original.Y m ≃* modelY S e :=
  (Original.Y m).equivMapOfInjective (wreathModelHom S e) (wreathModelHom_injective S e)


theorem modelY_unique_involution (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : y ∈ modelY S e) (horder : orderOf y = 2) :
    y = wreathModelHom S e (Original.x (2 ^ n)) := by
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
  have hworder : orderOf (⟨w, hw⟩ : Original.Y (2 ^ n)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ((orderOf_injective _ (wreathModelHom_injective S e) w).symm.trans horder)
  have hweq := originalY_unique_involution n hn ⟨w, hw⟩ hworder
  exact congrArg (fun a : Original.Y (2 ^ n) => wreathModelHom S e a) hweq

theorem modelY_center_map (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (Subgroup.center (modelY S e)).map (modelY S e).subtype =
      Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n))) := by
  rw [← Subgroup.map_center_eq (modelYEquiv S e), Subgroup.map_map]
  change (Subgroup.center (Original.Y (2 ^ n))).map
    ((wreathModelHom S e).comp (Original.Y (2 ^ n)).subtype) = _
  rw [← Subgroup.map_map, originalY_center_map n hn, MonoidHom.map_zpowers]

theorem modelCenter_inf_modelY (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelCenter S e ⊓ modelY S e =
      Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n))) := by
  rw [modelCenter, modelY, ← Subgroup.map_inf _ _ _ (wreathModelHom_injective S e),
    original_Z_inf_Y n hn, MonoidHom.map_zpowers]

theorem modelY_center_eq (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.center (modelY S e) =
      (Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))).subgroupOf (modelY S e) := by
  ext y
  change y ∈ Subgroup.center (modelY S e) ↔ y.val ∈
    Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))
  rw [← modelY_center_map n hn S e]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, heq⟩
    exact (Subtype.ext heq : z = y) ▸ hz


theorem originalYQuaternionEquiv_involution_eq (n : ℕ) (hn : 2 ≤ n) :
    originalYQuaternionEquiv n hn (QuaternionGroup.a ((2 ^ n / 2 : ℕ) :
      ZMod (2 * (2 ^ n / 2)))) = originalYInvolution n hn :=
  Subtype.ext (originalYQuaternionEquiv_involution n hn)

@[expose] def originalYCentralInvolution (n : ℕ) (hn : 2 ≤ n) :
    Subgroup (Original.Y (2 ^ n)) := Subgroup.zpowers (originalYInvolution n hn)


instance originalYCentralInvolution_normal_instance (n : ℕ) (hn : 2 ≤ n) :
    (originalYCentralInvolution n hn).Normal := by
  rw [originalYCentralInvolution, ← originalY_center_eq_zpowers n hn]
  infer_instance

theorem originalYQuaternionEquiv_map_center (n : ℕ) (hn : 2 ≤ n) :
    (CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ (2 ^ n / 2)).map
      (originalYQuaternionEquiv n hn).toMonoidHom = originalYCentralInvolution n hn := by
  rw [CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ, MonoidHom.map_zpowers]
  change Subgroup.zpowers ((originalYQuaternionEquiv n hn)
    (QuaternionGroup.a ((2 ^ n / 2 : ℕ) : ZMod (2 * (2 ^ n / 2))))) = _
  rw [originalYQuaternionEquiv_involution_eq]
  rfl

@[expose] def originalYDihedralEquiv (n : ℕ) (hn : 2 ≤ n) :
    Original.Y (2 ^ n) ⧸ originalYCentralInvolution n hn ≃* DihedralGroup (2 ^ n / 2) := by
  let : NeZero (2 ^ n / 2) := ⟨by
    have hge : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega⟩
  exact (QuotientGroup.congr
    (CFSG.Semidihedral.CentralQuotients.nativeQuaternionZ (2 ^ n / 2))
    (originalYCentralInvolution n hn)
    (originalYQuaternionEquiv n hn) (originalYQuaternionEquiv_map_center n hn)).symm.trans
    (CFSG.Semidihedral.CentralQuotients.nativeQuaternionQuotientEquiv (2 ^ n / 2)).symm


@[expose] def modelYInvolution (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : modelY S e :=
  modelYEquiv S e (originalYInvolution n hn)


@[expose] def modelYCentralInvolution (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : Subgroup (modelY S e) :=
  Subgroup.zpowers (modelYInvolution n hn S e)


theorem modelYEquiv_map_centralInvolution (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (originalYCentralInvolution n hn).map (modelYEquiv S e).toMonoidHom =
      modelYCentralInvolution n hn S e := by
  rw [originalYCentralInvolution, MonoidHom.map_zpowers]
  rfl

theorem modelYCentralInvolution_eq_center (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelYCentralInvolution n hn S e = Subgroup.center (modelY S e) := by
  rw [← modelYEquiv_map_centralInvolution n hn S e, originalYCentralInvolution,
    ← originalY_center_eq_zpowers n hn]
  exact Subgroup.map_center_eq (modelYEquiv S e)

instance modelYCentralInvolution_normal (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelYCentralInvolution n hn S e).Normal := by
  rw [modelYCentralInvolution_eq_center n hn S e]
  infer_instance

theorem modelYCentralInvolution_eq (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelYCentralInvolution n hn S e =
      (Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))).subgroupOf (modelY S e) := by
  rw [modelYCentralInvolution_eq_center n hn S e]
  exact modelY_center_eq n hn S e

@[expose] def modelYDihedralEquiv (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelY S e ⧸ modelYCentralInvolution n hn S e ≃* DihedralGroup (2 ^ n / 2) :=
  (QuotientGroup.congr (originalYCentralInvolution n hn) (modelYCentralInvolution n hn S e)
    (modelYEquiv S e) (modelYEquiv_map_centralInvolution n hn S e)).symm.trans
      (originalYDihedralEquiv n hn)


theorem original_a_mem_center (m : ℕ) :
    Original.a m ∈ Subgroup.center (Wreath m) := by
  rw [Original.a_eq, Subgroup.mem_center_iff]
  intro g
  obtain ⟨⟨a, b, c⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
  change element m a b c * element m 1 1 0 = element m 1 1 0 * element m a b c
  rcases swap_exponent_cases c with rfl | rfl
  · rw [element_base_mul, element_base_mul]
    congr 1 <;> abel
  · rw [element_swap_mul, element_base_mul, add_zero]
    congr 1 <;> abel

instance originalCyclicCenter_normal (m : ℕ) : (Original.Z m).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (original_a_mem_center m))

@[expose] def modelSylowCenter {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) : Subgroup S :=
  (modelCenter S e).subgroupOf (S : Subgroup G)

theorem modelSylowCenter_eq_map {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    modelSylowCenter S e = (Original.Z m).map e.symm.toMonoidHom := by
  ext s
  constructor
  · intro hs
    obtain ⟨z, hz, hval⟩ := Subgroup.mem_map.mp hs
    have heq : e.symm z = s := Subtype.ext hval
    exact Subgroup.mem_map.mpr ⟨z, hz, heq⟩
  · rintro ⟨z, hz, heq⟩
    change (s : G) ∈ modelCenter S e
    exact Subgroup.mem_map.mpr ⟨z, hz, congrArg Subtype.val heq⟩

instance modelSylowCenter_normal {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (modelSylowCenter S e).Normal := by
  rw [modelSylowCenter_eq_map]
  exact Subgroup.Normal.map inferInstance e.symm.toMonoidHom e.symm.surjective

theorem modelSylowCenter_eq_center (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelSylowCenter S e = Subgroup.center S := by
  rw [modelSylowCenter_eq_map, ← (wreath_center_involution_and_quaternion_coordinates n hn).center]
  exact Subgroup.map_center_eq e.symm

@[expose] def modelSylowDihedralEquiv (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    S ⧸ modelSylowCenter S e ≃* DihedralGroup (2 ^ n) :=
  (QuotientGroup.congr (Original.Z (2 ^ n)) (modelSylowCenter S e) e.symm
    (modelSylowCenter_eq_map S e).symm).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (wreath_center_involution_and_quaternion_coordinates n hn).center.symm).trans
        (centerQuotientEquivDihedral (2 ^ n) (by
          have hge : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
          omega)))


theorem centralizerQuaternion_unique_involution (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : involutionCentralizer n S e) (hy : y ∈ centralizerQuaternion n hn S e)
    (horder : orderOf y = 2) : y = centralInvolution n S e := by
  exact modelY_unique_involution n hn (centralizerSylow n hn S e)
    (centralizerCoordinates n hn S e) y hy horder


end CFSG.Wreathed
