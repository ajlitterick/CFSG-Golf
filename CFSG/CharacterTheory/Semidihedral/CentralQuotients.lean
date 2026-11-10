module

public import CFSG.CharacterTheory.Semidihedral.StructureTransport

public section

namespace CFSG.Semidihedral.CentralQuotients

open CFSG.Open
open DihedralQuaternion

@[expose] def periodReduction (d m : ℕ) (h : d ∣ m) : ZMod m →+* ZMod d :=
  ZMod.castHom h (ZMod d)

@[simp] theorem periodReduction_apply (d m : ℕ) [NeZero m] (h : d ∣ m) (i : ZMod m) :
    periodReduction d m h i = (i.val : ZMod d) := by
  rw [periodReduction, ZMod.castHom_apply, ZMod.cast_eq_val]

theorem periodReduction_eq_zero_iff (d m : ℕ) [NeZero d] [NeZero m]
    (hm : m = 2 * d) (i : ZMod m) :
    periodReduction d m (hm ▸ dvd_mul_left d 2) i = 0 ↔
      i = 0 ∨ i = (d : ZMod m) := by
  have hd : 0 < d := NeZero.pos d
  have hi := ZMod.val_lt i
  rw [periodReduction_apply, ZMod.natCast_eq_zero_iff]
  constructor
  · rintro ⟨a, ha⟩
    have ha2 : a < 2 := by
      rw [ha, hm] at hi
      nlinarith
    have ha01 : a = 0 ∨ a = 1 := by omega
    rcases ha01 with rfl | rfl
    · left
      apply ZMod.val_injective
      simpa using ha
    · right
      apply ZMod.val_injective
      rw [ZMod.val_natCast_of_lt (by rw [hm]; omega)]
      simpa using ha
  · rintro (rfl | rfl)
    · simp
    · rw [ZMod.val_natCast_of_lt (by rw [hm]; omega)]

@[expose] def centerZ (n : ℕ) (_hn : 4 ≤ n) : Subgroup (SemidihedralGroup n) :=
  Subgroup.zpowers (z n)

instance centerZ_normal (n : ℕ) (hn : 4 ≤ n) : (centerZ n hn).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (z_mem_center n hn))

theorem centerZ_eq_center (n : ℕ) (hn : 4 ≤ n) :
    centerZ n hn = Subgroup.center (SemidihedralGroup n) :=
  (center_eq_zpowers n hn).symm


@[expose] def semidihedralReduction (n : ℕ) (hn : 4 ≤ n) :
    ZMod (modulus n) →+* ZMod (half n) :=
  periodReduction (half n) (modulus n)
    (⟨2, by rw [modulus_eq_two_mul_half (by omega)]; omega⟩)

@[simp] theorem semidihedralReduction_twist (n : ℕ) (hn : 4 ≤ n) :
    semidihedralReduction n hn (twist n) = -1 := by
  rw [twist, map_sub, map_natCast, map_one, ZMod.natCast_self, zero_sub]

theorem semidihedralReduction_eq_zero_iff (n : ℕ) (hn : 4 ≤ n)
    (i : ZMod (modulus n)) :
    semidihedralReduction n hn i = 0 ↔
      i = 0 ∨ i = (half n : ZMod (modulus n)) :=
  periodReduction_eq_zero_iff (half n) (modulus n)
    (modulus_eq_two_mul_half (by omega)) i

@[expose] def reducedElement (n : ℕ) (hn : 4 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) : DihedralGroup (half n) :=
  if e = 0 then DihedralGroup.r (semidihedralReduction n hn i)
  else DihedralGroup.sr (-semidihedralReduction n hn i)

@[expose] def toDihedral (n : ℕ) (hn : 4 ≤ n) :
    SemidihedralGroup n →* DihedralGroup (half n) where
  toFun g := reducedElement n hn (coordinateEquiv n (by omega) g).1
    (coordinateEquiv n (by omega) g).2
  map_one' := by
    rw [← element_zero_zero n (by omega), coordinateEquiv_element]
    simp [reducedElement]
  map_mul' g h := by
    obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n (by omega)).symm.surjective g
    obtain ⟨⟨j, f⟩, rfl⟩ := (coordinateEquiv n (by omega)).symm.surjective h
    change reducedElement n hn
        (coordinateEquiv n (by omega) (element n (by omega) i e *
          element n (by omega) j f)).1
        (coordinateEquiv n (by omega) (element n (by omega) i e *
          element n (by omega) j f)).2 =
      reducedElement n hn (coordinateEquiv n (by omega) (element n (by omega) i e)).1
        (coordinateEquiv n (by omega) (element n (by omega) i e)).2 *
      reducedElement n hn (coordinateEquiv n (by omega) (element n (by omega) j f)).1
        (coordinateEquiv n (by omega) (element n (by omega) j f)).2
    rw [coordinateEquiv_element, coordinateEquiv_element]
    rcases exponent_cases e with rfl | rfl <;> rcases exponent_cases f with rfl | rfl
    · simp [element_rotation_mul, reducedElement, map_add]
    · simp [element_rotation_mul, reducedElement, map_add, neg_add_rev, sub_eq_add_neg,
        add_comm]
    · simp [element_reflection_mul, reducedElement, map_add, map_mul,
        semidihedralReduction_twist, add_comm]
    · simp [element_reflection_mul, reducedElement, map_add, map_mul,
        semidihedralReduction_twist, sub_eq_add_neg, add_comm,
        show (1 + 1 : ZMod 2) = 0 by decide]

@[simp] theorem toDihedral_element (n : ℕ) (hn : 4 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    toDihedral n hn (element n (by omega) i e) = reducedElement n hn i e := by
  change reducedElement n hn (coordinateEquiv n (by omega) (element n (by omega) i e)).1
    (coordinateEquiv n (by omega) (element n (by omega) i e)).2 = _
  rw [coordinateEquiv_element]

@[simp] theorem toDihedral_r (n : ℕ) (hn : 4 ≤ n) :
    toDihedral n hn (r n) = DihedralGroup.r 1 := by
  change reducedElement n hn (coordinateEquiv n (by omega) (r n)).1
    (coordinateEquiv n (by omega) (r n)).2 = _
  rw [coordinateEquiv_r]
  simp [reducedElement]

@[simp] theorem toDihedral_s (n : ℕ) (hn : 4 ≤ n) :
    toDihedral n hn (s n) = DihedralGroup.sr 0 := by
  change reducedElement n hn (coordinateEquiv n (by omega) (s n)).1
    (coordinateEquiv n (by omega) (s n)).2 = _
  rw [coordinateEquiv_s]
  simp [reducedElement]

theorem toDihedral_surjective (n : ℕ) (hn : 4 ≤ n) :
    Function.Surjective (toDihedral n hn) := by
  rintro (a | a)
  · refine ⟨element n (by omega) (a.val : ZMod (modulus n)) 0, ?_⟩
    simp [reducedElement]
  · refine ⟨element n (by omega) (-(a.val : ZMod (modulus n))) 1, ?_⟩
    simp [reducedElement]


theorem toDihedral_ker (n : ℕ) (hn : 4 ≤ n) :
    (toDihedral n hn).ker = Subgroup.zpowers (z n) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n (by omega)).symm.surjective g
    change element n (by omega) i e ∈ Subgroup.zpowers (z n)
    change toDihedral n hn (element n (by omega) i e) = 1 at hg
    rw [toDihedral_element] at hg
    rcases exponent_cases e with rfl | rfl
    · have hi : semidihedralReduction n hn i = 0 := by
        change DihedralGroup.r (semidihedralReduction n hn i) = DihedralGroup.r 0 at hg
        exact DihedralGroup.r.inj hg
      rcases (semidihedralReduction_eq_zero_iff n hn i).mp hi with rfl | rfl
      · rw [element_zero_zero]
        exact (Subgroup.zpowers (z n)).one_mem
      · rw [← z_eq_element n (by omega)]
        exact Subgroup.mem_zpowers _
    · simp only [reducedElement, one_ne_zero, ↓reduceIte] at hg
      cases hg
  · apply Subgroup.zpowers_le.mpr
    change toDihedral n hn (z n) = 1
    rw [z, map_pow, toDihedral_r, DihedralGroup.r_one_pow_n]

@[expose] noncomputable def dihedralQuotientEquiv (n : ℕ) (hn : 4 ≤ n) :
    DihedralGroup (half n) ≃* SemidihedralGroup n ⧸ centerZ n hn :=
  (QuotientGroup.liftEquiv (centerZ n hn) (toDihedral_surjective n hn)
    (toDihedral_ker n hn).symm).symm

@[simp] theorem dihedralQuotientEquiv_symm_mk (n : ℕ) (hn : 4 ≤ n)
    (g : SemidihedralGroup n) :
    (dihedralQuotientEquiv n hn).symm ((QuotientGroup.mk' (centerZ n hn)) g) =
      toDihedral n hn g := rfl

@[expose] def rZ (n : ℕ) (hn : 4 ≤ n) : SemidihedralGroup n ⧸ centerZ n hn :=
  QuotientGroup.mk' (centerZ n hn) (r n)

@[expose] def sZ (n : ℕ) (hn : 4 ≤ n) : SemidihedralGroup n ⧸ centerZ n hn :=
  QuotientGroup.mk' (centerZ n hn) (s n)

@[simp] theorem dihedralQuotientEquiv_rotation (n : ℕ) (hn : 4 ≤ n) :
    dihedralQuotientEquiv n hn (DihedralGroup.r 1) = rZ n hn := by
  apply (dihedralQuotientEquiv n hn).symm.injective
  rw [MulEquiv.symm_apply_apply]
  exact (toDihedral_r n hn).symm

@[simp] theorem dihedralQuotientEquiv_reflection (n : ℕ) (hn : 4 ≤ n) :
    dihedralQuotientEquiv n hn (DihedralGroup.sr 0) = sZ n hn := by
  apply (dihedralQuotientEquiv n hn).symm.injective
  rw [MulEquiv.symm_apply_apply]
  exact (toDihedral_s n hn).symm


theorem original_generators_closure (n : ℕ) (hn : 3 ≤ n) :
    Subgroup.closure {r n, s n} = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn).symm.surjective g
  change element n hn i e ∈ Subgroup.closure {r n, s n}
  rw [element_eq]
  exact Subgroup.mul_mem _
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)


@[expose] def nativeQuaternionZ (q : ℕ) : Subgroup (QuaternionGroup q) :=
  Subgroup.zpowers (QuaternionGroup.a (q : ZMod (2 * q)))

theorem nativeQuaternion_half_mem_center (q : ℕ) :
    QuaternionGroup.a (q : ZMod (2 * q)) ∈ Subgroup.center (QuaternionGroup q) := by
  rw [Subgroup.mem_center_iff]
  rintro (i | i)
  · simp [add_comm]
  · rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
    congr 1
    have hq : (q : ZMod (2 * q)) + q = 0 := by
      rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]
    linear_combination hq

instance nativeQuaternionZ_normal (q : ℕ) : (nativeQuaternionZ q).Normal :=
  Subgroup.normal_of_le_center
    (Subgroup.zpowers_le.mpr (nativeQuaternion_half_mem_center q))

@[expose] def quaternionToDihedral (q : ℕ) : QuaternionGroup q →* DihedralGroup q where
  toFun
    | QuaternionGroup.a i => DihedralGroup.r (periodReduction q (2 * q) (dvd_mul_left q 2) i)
    | QuaternionGroup.xa i => DihedralGroup.sr (periodReduction q (2 * q) (dvd_mul_left q 2) i)
  map_one' := by
    change DihedralGroup.r (periodReduction q (2 * q) (dvd_mul_left q 2) 0) = 1
    rw [map_zero, DihedralGroup.r_zero]
  map_mul' := by
    rintro (i | i) (j | j)
    · change DihedralGroup.r (periodReduction q (2 * q) (dvd_mul_left q 2) (i + j)) = _
      rw [map_add, DihedralGroup.r_mul_r]
    · change DihedralGroup.sr (periodReduction q (2 * q) (dvd_mul_left q 2) (j - i)) = _
      rw [map_sub, DihedralGroup.r_mul_sr]
    · change DihedralGroup.sr (periodReduction q (2 * q) (dvd_mul_left q 2) (i + j)) = _
      rw [map_add, DihedralGroup.sr_mul_r]
    · change DihedralGroup.r (periodReduction q (2 * q) (dvd_mul_left q 2) (q + j - i)) = _
      rw [map_sub, map_add, map_natCast, ZMod.natCast_self, zero_add,
        DihedralGroup.sr_mul_sr]

@[simp] theorem quaternionToDihedral_a (q : ℕ) (i : ZMod (2 * q)) :
    quaternionToDihedral q (QuaternionGroup.a i) =
      DihedralGroup.r (periodReduction q (2 * q) (dvd_mul_left q 2) i) := rfl

@[simp] theorem quaternionToDihedral_xa (q : ℕ) (i : ZMod (2 * q)) :
    quaternionToDihedral q (QuaternionGroup.xa i) =
      DihedralGroup.sr (periodReduction q (2 * q) (dvd_mul_left q 2) i) := rfl

@[simp] theorem quaternionToDihedral_rotation (q : ℕ) :
    quaternionToDihedral q (QuaternionGroup.a 1) = DihedralGroup.r 1 := by simp

@[simp] theorem quaternionToDihedral_generator (q : ℕ) :
    quaternionToDihedral q (QuaternionGroup.xa 0) = DihedralGroup.sr 0 := by simp

theorem quaternionToDihedral_surjective (q : ℕ) [NeZero q] :
    Function.Surjective (quaternionToDihedral q) := by
  rintro (i | i)
  · refine ⟨QuaternionGroup.a (i.val : ZMod (2 * q)), ?_⟩
    simp
  · refine ⟨QuaternionGroup.xa (i.val : ZMod (2 * q)), ?_⟩
    simp


theorem quaternionToDihedral_ker (q : ℕ) [NeZero q] :
    (quaternionToDihedral q).ker = nativeQuaternionZ q := by
  apply le_antisymm
  · rintro (i | i) hi
    · change DihedralGroup.r (periodReduction q (2 * q) (dvd_mul_left q 2) i) =
        DihedralGroup.r 0 at hi
      have hz := DihedralGroup.r.inj hi
      rcases (periodReduction_eq_zero_iff q (2 * q) rfl i).mp hz with rfl | rfl
      · exact (nativeQuaternionZ q).one_mem
      · exact Subgroup.mem_zpowers _
    · change DihedralGroup.sr (periodReduction q (2 * q) (dvd_mul_left q 2) i) =
        DihedralGroup.r 0 at hi
      cases hi
  · apply Subgroup.zpowers_le.mpr
    change quaternionToDihedral q (QuaternionGroup.a (q : ZMod (2 * q))) = 1
    rw [quaternionToDihedral_a, map_natCast, ZMod.natCast_self, DihedralGroup.r_zero]

@[expose] noncomputable def nativeQuaternionQuotientEquiv (q : ℕ) [NeZero q] :
    DihedralGroup q ≃* QuaternionGroup q ⧸ nativeQuaternionZ q :=
  (QuotientGroup.liftEquiv (nativeQuaternionZ q) (quaternionToDihedral_surjective q)
    (quaternionToDihedral_ker q).symm).symm

@[simp] theorem nativeQuaternionQuotientEquiv_symm_mk (q : ℕ) [NeZero q]
    (g : QuaternionGroup q) :
    (nativeQuaternionQuotientEquiv q).symm (QuotientGroup.mk' (nativeQuaternionZ q) g) =
      quaternionToDihedral q g := rfl

@[simp] theorem nativeQuaternionQuotientEquiv_rotation (q : ℕ) [NeZero q] :
    nativeQuaternionQuotientEquiv q (DihedralGroup.r 1) =
      QuotientGroup.mk' (nativeQuaternionZ q) (QuaternionGroup.a 1) := by
  apply (nativeQuaternionQuotientEquiv q).symm.injective
  rw [MulEquiv.symm_apply_apply, nativeQuaternionQuotientEquiv_symm_mk,
    quaternionToDihedral_rotation]

@[simp] theorem nativeQuaternionQuotientEquiv_generator (q : ℕ) [NeZero q] :
    nativeQuaternionQuotientEquiv q (DihedralGroup.sr 0) =
      QuotientGroup.mk' (nativeQuaternionZ q) (QuaternionGroup.xa 0) := by
  apply (nativeQuaternionQuotientEquiv q).symm.injective
  rw [MulEquiv.symm_apply_apply, nativeQuaternionQuotientEquiv_symm_mk,
    quaternionToDihedral_generator]

@[expose] def quaternionZ (n : ℕ) (hn : 4 ≤ n) : Subgroup (quaternionSubgroup n) :=
  (centerZ n hn).subgroupOf (quaternionSubgroup n)

instance quaternionZ_normal (n : ℕ) (hn : 4 ≤ n) : (quaternionZ n hn).Normal := by
  change ((centerZ n hn).comap (quaternionSubgroup n).subtype).Normal
  infer_instance

theorem centerZ_le_quaternionSubgroup (n : ℕ) (hn : 4 ≤ n) :
    centerZ n hn ≤ quaternionSubgroup n := by
  apply Subgroup.zpowers_le.mpr
  change r n ^ half n ∈ quaternionSubgroup n
  rw [half_eq_two_mul_parameter n (by omega), pow_mul]
  exact (quaternionSubgroup n).pow_mem (r_sq_mem_quaternionSubgroup n) _

@[expose] def quaternionX (n : ℕ) : quaternionSubgroup n :=
  ⟨r n ^ 2, r_sq_mem_quaternionSubgroup n⟩

@[expose] def quaternionY (n : ℕ) : quaternionSubgroup n :=
  ⟨r n * s n, rs_mem_quaternionSubgroup n⟩

@[expose] def quaternionInvolution (n : ℕ) (hn : 4 ≤ n) : quaternionSubgroup n :=
  ⟨z n, centerZ_le_quaternionSubgroup n hn (Subgroup.mem_zpowers _)⟩

theorem quaternionZ_eq_zpowers (n : ℕ) (hn : 4 ≤ n) :
    quaternionZ n hn = Subgroup.zpowers (quaternionInvolution n hn) := by
  apply Subgroup.map_injective (quaternionSubgroup n).subtype_injective
  rw [quaternionZ, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le
    (centerZ_le_quaternionSubgroup n hn)]
  rfl

@[simp] theorem quaternionEquiv_involution (n : ℕ) (hn : 4 ≤ n) :
    quaternionEquiv n hn (QuaternionGroup.a (2 ^ (n - 3) : ℕ)) =
      quaternionInvolution n hn := by
  apply Subtype.ext
  rw [quaternionEquiv_coe, quaternionHom_a, quaternionCoordinate_parameter,
    ← z_eq_element n (by omega)]
  rfl

theorem map_nativeQuaternionZ (n : ℕ) (hn : 4 ≤ n) :
    (nativeQuaternionZ (2 ^ (n - 3))).map (↑(quaternionEquiv n hn)) =
      quaternionZ n hn := by
  rw [nativeQuaternionZ, MonoidHom.map_zpowers]
  change Subgroup.zpowers (quaternionEquiv n hn (QuaternionGroup.a (2 ^ (n - 3) : ℕ))) = _
  rw [quaternionEquiv_involution, quaternionZ_eq_zpowers]

@[expose] noncomputable def quaternionQuotientEquiv (n : ℕ) (hn : 4 ≤ n) :
    DihedralGroup (2 ^ (n - 3)) ≃* quaternionSubgroup n ⧸ quaternionZ n hn :=
  (nativeQuaternionQuotientEquiv (2 ^ (n - 3))).trans
    (QuotientGroup.congr (nativeQuaternionZ (2 ^ (n - 3))) (quaternionZ n hn)
      (quaternionEquiv n hn) (map_nativeQuaternionZ n hn))

@[expose] def xZ (n : ℕ) (hn : 4 ≤ n) : quaternionSubgroup n ⧸ quaternionZ n hn :=
  QuotientGroup.mk' (quaternionZ n hn) (quaternionX n)

@[expose] def yZ (n : ℕ) (hn : 4 ≤ n) : quaternionSubgroup n ⧸ quaternionZ n hn :=
  QuotientGroup.mk' (quaternionZ n hn) (quaternionY n)

@[simp] theorem quaternionQuotientEquiv_rotation (n : ℕ) (hn : 4 ≤ n) :
    quaternionQuotientEquiv n hn (DihedralGroup.r 1) = xZ n hn := by
  rw [quaternionQuotientEquiv, MulEquiv.trans_apply,
    nativeQuaternionQuotientEquiv_rotation, QuotientGroup.congr_mk']
  congr 1
  apply Subtype.ext
  exact quaternionEquiv_rotation n hn

@[simp] theorem quaternionQuotientEquiv_generator (n : ℕ) (hn : 4 ≤ n) :
    quaternionQuotientEquiv n hn (DihedralGroup.sr 0) = yZ n hn := by
  rw [quaternionQuotientEquiv, MulEquiv.trans_apply,
    nativeQuaternionQuotientEquiv_generator, QuotientGroup.congr_mk']
  congr 1
  apply Subtype.ext
  exact quaternionEquiv_generator n hn


theorem nativeQuaternion_center (q : ℕ) (hq : 2 ≤ q) :
    Subgroup.center (QuaternionGroup q) = nativeQuaternionZ q := by
  let : NeZero q := ⟨by omega⟩
  apply le_antisymm
  · rintro (i | i) hi
    · have hc := Subgroup.mem_center_iff.mp hi (QuaternionGroup.xa 0)
      rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa, zero_add, zero_sub] at hc
      have htwo : 2 * i = 0 := by
        have he := QuaternionGroup.xa.inj hc
        linear_combination he
      have hd : q ∣ i.val := by
        have hz : ((2 * i.val : ℕ) : ZMod (2 * q)) = 0 := by
          simpa only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using htwo
        have hdiv := (ZMod.natCast_eq_zero_iff (2 * i.val) (2 * q)).mp hz
        exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < (2 : ℕ))).mp hdiv
      have hr : periodReduction q (2 * q) (dvd_mul_left q 2) i = 0 := by
        rw [periodReduction_apply, ZMod.natCast_eq_zero_iff]
        exact hd
      rcases (periodReduction_eq_zero_iff q (2 * q) rfl i).mp hr with rfl | rfl
      · exact (nativeQuaternionZ q).one_mem
      · exact Subgroup.mem_zpowers _
    · have hc := Subgroup.mem_center_iff.mp hi (QuaternionGroup.a 1)
      rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hc
      have htwo : (2 : ZMod (2 * q)) = 0 := by
        have he := QuaternionGroup.xa.inj hc
        linear_combination -he
      have hd := (ZMod.natCast_eq_zero_iff 2 (2 * q)).mp htwo
      exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < (2 : ℕ)) (by omega) hd).elim
  · exact Subgroup.zpowers_le.mpr (nativeQuaternion_half_mem_center q)


@[expose] def ambientZ {H : Type*} [Group H] (t : H)
    (_htc : t ∈ Subgroup.center H) : Subgroup H := Subgroup.zpowers t

instance ambientZ_normal {H : Type*} [Group H] (t : H)
    (htc : t ∈ Subgroup.center H) : (ambientZ t htc).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr htc)

theorem ambientZ_natCard {H : Type*} [Group H] (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    Nat.card (ambientZ t htc) = 2 := by
  rw [ambientZ, Nat.card_zpowers, ht]

theorem ambientZ_le_sylow {H : Type*} [Group H] (S : Sylow 2 H) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    ambientZ t htc ≤ (S : Subgroup H) := by
  have hp : IsPGroup 2 (ambientZ t htc) := IsPGroup.of_card
    (show Nat.card (ambientZ t htc) = 2 ^ 1 by rw [ambientZ_natCard t htc ht]; rfl)
  exact hp.le_sylow_of_normal S

theorem centralInvolution_mem_sylow {H : Type*} [Group H] (S : Sylow 2 H) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) : t ∈ S :=
  ambientZ_le_sylow S t htc ht (Subgroup.mem_zpowers t)

@[expose] def sylowInvolution {H : Type*} [Group H] (S : Sylow 2 H) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) : S :=
  ⟨t, centralInvolution_mem_sylow S t htc ht⟩

theorem sylowInvolution_mem_center {H : Type*} [Group H] (S : Sylow 2 H) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    sylowInvolution S t htc ht ∈ Subgroup.center S := by
  apply (Subgroup.mem_center_iff (G := S)).mpr
  intro a
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp htc (a : H)

theorem original_center_unique_involution (n : ℕ) (hn : 4 ≤ n)
    (g : SemidihedralGroup n) (hgc : g ∈ Subgroup.center (SemidihedralGroup n))
    (hg : orderOf g = 2) : g = z n := by
  have hn3 : 3 ≤ n := Nat.le_trans (by decide) hn
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn3).symm.surjective g
  change element n hn3 i e = z n
  change element n hn3 i e ∈ Subgroup.center (SemidihedralGroup n) at hgc
  rcases (element_mem_center_iff n hn i e).mp hgc with ⟨rfl, rfl | rfl⟩
  · change orderOf (element n hn3 0 0) = 2 at hg
    rw [element_zero_zero, orderOf_one] at hg
    omega
  · exact (z_eq_element n hn3).symm

theorem supplied_z_eq_involution {H : Type*} [Group H] (S : Sylow 2 H)
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    f (z n) = sylowInvolution S t htc ht := by
  have hc : f.symm (sylowInvolution S t htc ht) ∈
      Subgroup.center (SemidihedralGroup n) := by
    rw [← Subgroup.map_center_eq f.symm]
    exact ⟨sylowInvolution S t htc ht, sylowInvolution_mem_center S t htc ht, rfl⟩
  have ho : orderOf (f.symm (sylowInvolution S t htc ht)) = 2 := by
    rw [equiv_orderOf]
    have h := orderOf_injective (S : Subgroup H).subtype
      (S : Subgroup H).subtype_injective (sylowInvolution S t htc ht)
    change orderOf t = orderOf (sylowInvolution S t htc ht) at h
    rw [← h, ht]
  have hz := original_center_unique_involution n hn _ hc ho
  apply f.symm.injective
  rw [MulEquiv.symm_apply_apply]
  exact hz.symm

@[expose] def sylowZ {H : Type*} [Group H] (S : Sylow 2 H) (t : H)
    (htc : t ∈ Subgroup.center H) : Subgroup S :=
  (ambientZ t htc).subgroupOf (S : Subgroup H)

instance sylowZ_normal {H : Type*} [Group H] (S : Sylow 2 H) (t : H)
    (htc : t ∈ Subgroup.center H) : (sylowZ S t htc).Normal := by
  change ((ambientZ t htc).comap (S : Subgroup H).subtype).Normal
  infer_instance

theorem sylowZ_eq_zpowers {H : Type*} [Group H] (S : Sylow 2 H) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    sylowZ S t htc = Subgroup.zpowers (sylowInvolution S t htc ht) := by
  apply Subgroup.map_injective (S : Subgroup H).subtype_injective
  rw [sylowZ, MonoidHom.map_zpowers,
    Subgroup.map_subgroupOf_eq_of_le (ambientZ_le_sylow S t htc ht)]
  rfl

theorem supplied_sylow_center {H : Type*} [Group H] (S : Sylow 2 H)
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    Subgroup.center S = Subgroup.zpowers (sylowInvolution S t htc ht) := by
  rw [← Subgroup.map_center_eq f, center_eq_zpowers n hn, MonoidHom.map_zpowers]
  change Subgroup.zpowers (f (z n)) = _
  rw [supplied_z_eq_involution S n hn f t htc ht]

theorem sylowZ_eq_center {H : Type*} [Group H] (S : Sylow 2 H)
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    sylowZ S t htc = Subgroup.center S := by
  rw [sylowZ_eq_zpowers S t htc ht, supplied_sylow_center S n hn f t htc ht]

theorem map_centerZ_to_sylowZ {H : Type*} [Group H] (S : Sylow 2 H)
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    (centerZ n hn).map (↑f) = sylowZ S t htc := by
  rw [centerZ_eq_center, Subgroup.map_center_eq,
    sylowZ_eq_center S n hn f t htc ht]

@[expose] noncomputable def suppliedCenterQuotientEquiv {H : Type*} [Group H]
    (S : Sylow 2 H) (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    DihedralGroup (half n) ≃* S ⧸ sylowZ S t htc :=
  (dihedralQuotientEquiv n hn).trans
    (QuotientGroup.congr (centerZ n hn) (sylowZ S t htc) f
      (map_centerZ_to_sylowZ S n hn f t htc ht))

@[simp] theorem suppliedCenterQuotientEquiv_rotation {H : Type*} [Group H]
    (S : Sylow 2 H) (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    suppliedCenterQuotientEquiv S n hn f t htc ht (DihedralGroup.r 1) =
      QuotientGroup.mk' (sylowZ S t htc) (f (r n)) := by
  rw [suppliedCenterQuotientEquiv, MulEquiv.trans_apply, dihedralQuotientEquiv_rotation]
  rfl

@[simp] theorem suppliedCenterQuotientEquiv_reflection {H : Type*} [Group H]
    (S : Sylow 2 H) (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    suppliedCenterQuotientEquiv S n hn f t htc ht (DihedralGroup.sr 0) =
      QuotientGroup.mk' (sylowZ S t htc) (f (s n)) := by
  rw [suppliedCenterQuotientEquiv, MulEquiv.trans_apply, dihedralQuotientEquiv_reflection]
  rfl

@[expose] def quotientSylow {H : Type*} [Group H] [Finite H] (S : Sylow 2 H) (t : H)
    (htc : t ∈ Subgroup.center H) : Sylow 2 (H ⧸ ambientZ t htc) :=
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  S.mapSurjective (QuotientGroup.mk'_surjective (ambientZ t htc))


@[expose] def quotientToSylow {H : Type*} [Group H] [Finite H] (S : Sylow 2 H) (t : H)
    (htc : t ∈ Subgroup.center H) : S →* quotientSylow S t htc :=
  ((QuotientGroup.mk' (ambientZ t htc)).domRestrict (S : Subgroup H)).codRestrict
    (quotientSylow S t htc : Subgroup (H ⧸ ambientZ t htc))
    (fun a => ⟨a, a.property, rfl⟩)

@[simp] theorem quotientToSylow_coe {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (t : H) (htc : t ∈ Subgroup.center H) (a : S) :
    (quotientToSylow S t htc a : H ⧸ ambientZ t htc) =
      QuotientGroup.mk' (ambientZ t htc) (a : H) := rfl

theorem quotientToSylow_surjective {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (t : H) (htc : t ∈ Subgroup.center H) :
    Function.Surjective (quotientToSylow S t htc) := by
  rintro ⟨b, hb⟩
  change b ∈ (S : Subgroup H).map (QuotientGroup.mk' (ambientZ t htc)) at hb
  rcases hb with ⟨a, ha, he⟩
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

theorem quotientToSylow_ker {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (t : H) (htc : t ∈ Subgroup.center H) :
    (quotientToSylow S t htc).ker = sylowZ S t htc := by
  ext a
  change quotientToSylow S t htc a = 1 ↔ (a : H) ∈ ambientZ t htc
  rw [Subtype.ext_iff]
  change QuotientGroup.mk' (ambientZ t htc) (a : H) = 1 ↔ (a : H) ∈ ambientZ t htc
  exact QuotientGroup.eq_one_iff _

@[expose] noncomputable def sylowQuotientEquivImage {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (t : H) (htc : t ∈ Subgroup.center H) :
    S ⧸ sylowZ S t htc ≃* quotientSylow S t htc :=
  QuotientGroup.liftEquiv (sylowZ S t htc) (quotientToSylow_surjective S t htc)
    (quotientToSylow_ker S t htc).symm

@[simp] theorem sylowQuotientEquivImage_mk {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (t : H) (htc : t ∈ Subgroup.center H) (a : S) :
    sylowQuotientEquivImage S t htc (QuotientGroup.mk' (sylowZ S t htc) a) =
      quotientToSylow S t htc a := rfl

@[expose] noncomputable def ambientDihedralEquiv {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    DihedralGroup (half n) ≃* quotientSylow S t htc :=
  (suppliedCenterQuotientEquiv S n hn f t htc ht).trans (sylowQuotientEquivImage S t htc)

@[simp] theorem ambientDihedralEquiv_rotation {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    ambientDihedralEquiv S n hn f t htc ht (DihedralGroup.r 1) =
      quotientToSylow S t htc (f (r n)) := by
  rw [ambientDihedralEquiv, MulEquiv.trans_apply, suppliedCenterQuotientEquiv_rotation,
    sylowQuotientEquivImage_mk]

@[simp] theorem ambientDihedralEquiv_reflection {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    ambientDihedralEquiv S n hn f t htc ht (DihedralGroup.sr 0) =
      quotientToSylow S t htc (f (s n)) := by
  rw [ambientDihedralEquiv, MulEquiv.trans_apply, suppliedCenterQuotientEquiv_reflection,
    sylowQuotientEquivImage_mk]


theorem ambient_quotient_reflection_order {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (t : H)
    (htc : t ∈ Subgroup.center H) (ht : orderOf t = 2) :
    orderOf (QuotientGroup.mk' (ambientZ t htc) (f (s n) : H)) = 2 := by
  have h := orderOf_injective (quotientSylow S t htc : Subgroup (H ⧸ ambientZ t htc)).subtype
    (quotientSylow S t htc : Subgroup (H ⧸ ambientZ t htc)).subtype_injective
    (quotientToSylow S t htc (f (s n)))
  change orderOf (QuotientGroup.mk' (ambientZ t htc) (f (s n) : H)) =
    orderOf (quotientToSylow S t htc (f (s n))) at h
  rw [h, ← ambientDihedralEquiv_reflection S n hn f t htc ht, equiv_orderOf,
    DihedralGroup.orderOf_sr]


end CFSG.Semidihedral.CentralQuotients
