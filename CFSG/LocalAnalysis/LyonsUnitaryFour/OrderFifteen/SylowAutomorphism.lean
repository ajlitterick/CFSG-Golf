module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryOvergroup.Automorphism
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Sylow

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.RankTwoShapes CFSG.RankTwoShapes.UnitaryFourW

noncomputable section

instance mulAut_conj_range_normal (P : Type*) [Group P] :
    (MulAut.conj : P →* MulAut P).range.Normal where
  conj_mem := by
    rintro _ ⟨p, rfl⟩ φ
    refine ⟨φ p, ?_⟩
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]

section FieldSixteen

variable {K : Type} [Field K]

theorem fieldSixteen_add_pow_two_pow (hK : Nat.card K = 16) (x y : K) (j : ℕ) :
    (x + y) ^ 2 ^ j = x ^ 2 ^ j + y ^ 2 ^ j := by
  have := charP_two_of_natCard_eq_sixteen hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact add_pow_char_pow x y 2 j

theorem fieldSixteen_pow_two_pow_mod_four (hK : Nat.card K = 16) (x : K) (n : ℕ) :
    x ^ 2 ^ n = x ^ 2 ^ (n % 4) := by
  have key : ∀ q : ℕ, x ^ 2 ^ (4 * q) = x := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show 4 * (q + 1) = 4 * q + 4 by ring, pow_add, pow_mul x, ih,
        show (2 : ℕ) ^ 4 = 16 by norm_num]
      exact pow_sixteen_eq_self hK x
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul x, key]

theorem perm_pow_semilinear (σ : Equiv.Perm K) (c : Kˣ) (j : ℕ)
    (hσ : ∀ x, σ x = c * x ^ 2 ^ j) (n : ℕ) :
    ∃ d : Kˣ, ∀ x, (σ ^ n) x = d * x ^ 2 ^ (n * j) := by
  induction n with
  | zero => exact ⟨1, fun x => by simp⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨c * d ^ 2 ^ j, fun x => ?_⟩
    rw [pow_succ', Equiv.Perm.mul_apply, hd, hσ, Units.val_mul, Units.val_pow_eq_pow_val,
      mul_pow, ← pow_mul, ← pow_add, add_mul, one_mul]
    ring

theorem semilinear_eq_zero_of_odd_orderOf (hK : Nat.card K = 16) (σ : Equiv.Perm K) (c : Kˣ)
    (j : Fin 4) (hσ : ∀ x, σ x = c * x ^ 2 ^ (j : ℕ)) (hodd : Odd (orderOf σ)) : j = 0 := by
  obtain ⟨d, hd⟩ := perm_pow_semilinear σ c j hσ (orderOf σ)
  rw [pow_orderOf_eq_one] at hd
  have h : ∀ z : K, (1 : K) * z ^ 2 ^ ((0 : Fin 4) : ℕ) =
      d * z ^ 2 ^ ((⟨orderOf σ * j % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) : ℕ) := by
    intro z
    have := hd z
    rw [Equiv.Perm.one_apply, fieldSixteen_pow_two_pow_mod_four hK] at this
    simpa using this
  obtain ⟨-, h0⟩ := eq_and_eq_of_mul_pow_two_pow_eq hK one_ne_zero h
  have h4 : 4 ∣ orderOf σ * j := by
    have := congrArg Fin.val h0
    simp only [Fin.val_zero] at this
    omega
  have hcop : Nat.Coprime 4 (orderOf σ) :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
  have hj := hcop.dvd_of_dvd_mul_left h4
  exact Fin.ext (by have := j.2; simp only [Fin.val_zero]; omega)

end FieldSixteen

variable {K : Type} [Field K] {hK : Nat.card K = 16}

@[expose] def IsAutData (α : MulAut (unitaryFourW K hK)) (c : Kˣ) (j : Fin 4)
    (f : K →+ fieldSixteenSubfield hK) : Prop :=
  ∀ w, fst (α w) = (c : K) * fst w ^ 2 ^ (j : ℕ) ∧
    snd (α w) = (c : K) ^ 5 * snd w ^ 2 ^ (j : ℕ) + (f (fst w) : K)

theorem autDataFun_trace (c : Kˣ) (j : ℕ) (f : K →+ fieldSixteenSubfield hK)
    (w : unitaryFourW K hK) :
    ((c : K) ^ 5 * snd w ^ 2 ^ j + (f (fst w) : K)) +
        ((c : K) ^ 5 * snd w ^ 2 ^ j + (f (fst w) : K)) ^ 4 =
      ((c : K) * fst w ^ 2 ^ j) ^ 5 := by
  have := charP_two_of_natCard_eq_sixteen hK
  have hB : ((f (fst w) : K)) ^ 4 = f (fst w) := mem_fieldSixteenSubfield.mp (f (fst w)).2
  have hc : ((c : K) ^ 5) ^ 4 = (c : K) ^ 5 := pow_five_pow_four hK c
  have hfr : snd w ^ 2 ^ j + (snd w ^ 4) ^ 2 ^ j = (fst w ^ 5) ^ 2 ^ j := by
    rw [← fieldSixteen_add_pow_two_pow hK, snd_add_snd_pow_four]
  have e1 := add_pow_four_of_charTwo ((c : K) ^ 5 * snd w ^ 2 ^ j) (f (fst w) : K)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination e1 + hB + (snd w ^ 2 ^ j) ^ 4 * hc + (c : K) ^ 5 * hfr +
    (f (fst w) : K) * h2

@[expose] def autDataFun (c : Kˣ) (j : ℕ) (f : K →+ fieldSixteenSubfield hK)
    (w : unitaryFourW K hK) : unitaryFourW K hK :=
  mk hK ((c : K) * fst w ^ 2 ^ j) ((c : K) ^ 5 * snd w ^ 2 ^ j + (f (fst w) : K))
    (autDataFun_trace c j f w)

@[simp] theorem fst_autDataFun (c : Kˣ) (j : ℕ) (f : K →+ fieldSixteenSubfield hK)
    (w : unitaryFourW K hK) : fst (autDataFun c j f w) = (c : K) * fst w ^ 2 ^ j :=
  fst_mk _ _ _

@[simp] theorem snd_autDataFun (c : Kˣ) (j : ℕ) (f : K →+ fieldSixteenSubfield hK)
    (w : unitaryFourW K hK) :
    snd (autDataFun c j f w) = (c : K) ^ 5 * snd w ^ 2 ^ j + (f (fst w) : K) :=
  snd_mk _ _ _

theorem autDataFun_mul (c : Kˣ) (j : ℕ) (f : K →+ fieldSixteenSubfield hK)
    (v w : unitaryFourW K hK) :
    autDataFun c j f (v * w) = autDataFun c j f v * autDataFun c j f w := by
  ext
  · rw [fst_autDataFun, fst_mul, fst_mul, fst_autDataFun, fst_autDataFun,
      fieldSixteen_add_pow_two_pow hK, mul_add]
  · rw [snd_autDataFun, snd_mul, snd_mul, fst_mul, snd_autDataFun, snd_autDataFun,
      fst_autDataFun, fst_autDataFun, fieldSixteen_add_pow_two_pow hK,
      fieldSixteen_add_pow_two_pow hK, mul_pow, map_add, Subfield.coe_add]
    ring

theorem autDataFun_injective (c : Kˣ) (j : ℕ) (f : K →+ fieldSixteenSubfield hK) :
    Function.Injective (autDataFun c j f) := by
  have := charP_two_of_natCard_eq_sixteen hK
  intro v w h
  have h1 := congrArg fst h
  have h2 := congrArg snd h
  rw [fst_autDataFun, fst_autDataFun] at h1
  have ha : fst v = fst w := pow_two_pow_injective_of_charTwo j (mul_left_cancel₀ c.ne_zero h1)
  rw [snd_autDataFun, snd_autDataFun, ha, add_left_inj] at h2
  have hb : snd v = snd w :=
    pow_two_pow_injective_of_charTwo j (mul_left_cancel₀ (pow_ne_zero 5 c.ne_zero) h2)
  exact UnitaryFourW.ext ha hb

@[expose] def autOfData (c : Kˣ) (j : Fin 4) (f : K →+ fieldSixteenSubfield hK) :
    MulAut (unitaryFourW K hK) :=
  MulEquiv.ofBijective (MulHom.mk (autDataFun c j f) (autDataFun_mul c j f))
    ((@Finite.injective_iff_bijective _ UnitaryFourW.finite_unitaryFourW _).mp
      (autDataFun_injective c j f))

@[simp] theorem autOfData_apply (c : Kˣ) (j : Fin 4) (f : K →+ fieldSixteenSubfield hK)
    (w : unitaryFourW K hK) : autOfData c j f w = autDataFun c j f w :=
  rfl


theorem exists_isAutData (α : MulAut (unitaryFourW K hK)) :
    ∃ (c : Kˣ) (j : Fin 4) (f : K →+ fieldSixteenSubfield hK), IsAutData α c j f := by
  have := charP_two_of_natCard_eq_sixteen hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨c, j, hA, hB⟩ := exists_units_fin_four_of_mulEquiv α
  set D : unitaryFourW K hK → K := fun w => snd (α w) + (c : K) ^ 5 * snd w ^ 2 ^ (j : ℕ)
    with hD
  have hjpos : (2 : ℕ) ^ (j : ℕ) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hDz : ∀ v z, fst z = 0 → D (v * z) = D v := by
    intro v z hz
    have hαz : fst (α z) = 0 := by rw [hA, hz, zero_pow hjpos, mul_zero]
    simp only [hD, map_mul, snd_mul, hαz, mul_zero, add_zero, hz, hB z hz,
      fieldSixteen_add_pow_two_pow hK]
    linear_combination ((c : K) ^ 5 * snd z ^ 2 ^ (j : ℕ)) * h2
  have hDconst : ∀ v w, fst v = fst w → D v = D w := by
    intro v w hvw
    have hz : fst (v⁻¹ * w) = 0 := by
      rw [fst_mul, fst_inv, hvw]
      exact CharTwo.add_self_eq_zero _
    have := hDz v (v⁻¹ * w) hz
    rw [mul_inv_cancel_left] at this
    exact this.symm
  have hDmul : ∀ v w, D (v * w) = D v + D w := by
    intro v w
    simp only [hD, map_mul, snd_mul, hA, fieldSixteen_add_pow_two_pow hK, mul_pow]
    linear_combination ((c : K) ^ 5 * (fst v ^ 4) ^ 2 ^ (j : ℕ) * fst w ^ 2 ^ (j : ℕ)) * h2
  have hDmem : ∀ w, D w ^ 4 = D w := by
    intro w
    have h1 := snd_add_snd_pow_four (α w)
    rw [hA] at h1
    have hc : ((c : K) ^ 5) ^ 4 = (c : K) ^ 5 := pow_five_pow_four hK c
    have hfr : snd w ^ 2 ^ (j : ℕ) + (snd w ^ 4) ^ 2 ^ (j : ℕ) = (fst w ^ 5) ^ 2 ^ (j : ℕ) := by
      rw [← fieldSixteen_add_pow_two_pow hK, snd_add_snd_pow_four]
    have e1 := add_pow_four_of_charTwo (snd (α w)) ((c : K) ^ 5 * snd w ^ 2 ^ (j : ℕ))
    simp only [hD]
    linear_combination e1 + h1 + (snd w ^ 2 ^ (j : ℕ)) ^ 4 * hc + (c : K) ^ 5 * hfr +
      ((c : K) ^ 5 * (fst w ^ 2 ^ (j : ℕ)) ^ 5 - snd (α w) -
        (c : K) ^ 5 * snd w ^ 2 ^ (j : ℕ)) * h2
  have hD1 : D 1 = 0 := by
    simp only [hD, map_one, snd_one, zero_pow hjpos, mul_zero, add_zero]
  let f : K →+ fieldSixteenSubfield hK :=
    { toFun := fun a => ⟨D (exists_fst_eq (hK := hK) a).choose,
        mem_fieldSixteenSubfield.mpr (hDmem _)⟩
      map_zero' := by
        apply Subtype.ext
        change D _ = 0
        rw [hDconst _ 1 ((exists_fst_eq (hK := hK) 0).choose_spec.trans fst_one.symm), hD1]
      map_add' := fun a b => by
        apply Subtype.ext
        change D _ = D _ + D _
        rw [← hDmul]
        exact hDconst _ _ (by
          rw [fst_mul, (exists_fst_eq (hK := hK) a).choose_spec,
            (exists_fst_eq (hK := hK) b).choose_spec,
            (exists_fst_eq (hK := hK) (a + b)).choose_spec]) }
  refine ⟨c, j, f, fun w => ⟨hA w, ?_⟩⟩
  have hfw : (f (fst w) : K) = D w :=
    hDconst _ _ (exists_fst_eq (hK := hK) (fst w)).choose_spec
  rw [hfw]
  simp only [hD]
  linear_combination (-((c : K) ^ 5 * snd w ^ 2 ^ (j : ℕ))) * h2


@[expose] def firstCoordAction (hK : Nat.card K = 16) :
    MulAut (unitaryFourW K hK) →* Equiv.Perm K where
  toFun α :=
    { toFun := inducedFst α
      invFun := inducedFst α⁻¹
      left_inv := fun x => by
        obtain ⟨w, rfl⟩ := exists_fst_eq (hK := hK) x
        rw [inducedFst_fst, inducedFst_fst, MulAut.inv_apply, MulEquiv.symm_apply_apply]
      right_inv := fun x => by
        obtain ⟨w, rfl⟩ := exists_fst_eq (hK := hK) x
        rw [inducedFst_fst, inducedFst_fst, MulAut.inv_apply, MulEquiv.apply_symm_apply] }
  map_one' := Equiv.ext fun x => by
    obtain ⟨w, rfl⟩ := exists_fst_eq (hK := hK) x
    change inducedFst 1 (fst w) = fst w
    rw [inducedFst_fst, MulAut.one_apply]
  map_mul' α β := Equiv.ext fun x => by
    obtain ⟨w, rfl⟩ := exists_fst_eq (hK := hK) x
    change inducedFst (α * β) (fst w) = inducedFst α (inducedFst β (fst w))
    rw [inducedFst_fst, inducedFst_fst, inducedFst_fst, MulAut.mul_apply]

@[simp] theorem firstCoordAction_apply_fst (α : MulAut (unitaryFourW K hK))
    (w : unitaryFourW K hK) : firstCoordAction hK α (fst w) = fst (α w) :=
  inducedFst_fst α w

theorem ker_firstCoordAction : (firstCoordAction hK).ker = firstCoordFixing hK := by
  ext α
  rw [MonoidHom.mem_ker, mem_firstCoordFixing]
  constructor
  · intro h w
    rw [← firstCoordAction_apply_fst, h, Equiv.Perm.one_apply]
  · intro h
    ext x
    obtain ⟨w, rfl⟩ := exists_fst_eq (hK := hK) x
    rw [firstCoordAction_apply_fst, h, Equiv.Perm.one_apply]

theorem mem_range_firstCoordAction_iff (σ : Equiv.Perm K) :
    σ ∈ (firstCoordAction hK).range ↔ ∃ (c : Kˣ) (j : Fin 4), ∀ x, σ x = c * x ^ 2 ^ (j : ℕ) := by
  constructor
  · rintro ⟨α, rfl⟩
    obtain ⟨c, j, f, h⟩ := exists_isAutData α
    refine ⟨c, j, fun x => ?_⟩
    obtain ⟨w, rfl⟩ := exists_fst_eq (hK := hK) x
    rw [firstCoordAction_apply_fst, (h w).1]
  · rintro ⟨c, j, h⟩
    refine ⟨autOfData c j 0, Equiv.ext fun x => ?_⟩
    obtain ⟨w, rfl⟩ := exists_fst_eq (hK := hK) x
    rw [firstCoordAction_apply_fst, autOfData_apply, fst_autDataFun, h]


theorem odd_subgroup_outer_unitaryFourW {P : Type*} [Group P] (e : P ≃* unitaryFourW K hK)
    (H : Subgroup (MulAut P ⧸ (MulAut.conj : P →* MulAut P).range)) (hH : Odd (Nat.card H)) :
    IsCyclic H ∧ Nat.card H ∣ 15 := by
  classical
  have := finite_of_natCard_eq_sixteen hK
  have := charP_two_of_natCard_eq_sixteen hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set ψ : MulAut P →* Equiv.Perm K :=
    (firstCoordAction hK).comp (MulAut.congr e).toMonoidHom with hψ
  have hψapp : ∀ (α : MulAut P) (w : unitaryFourW K hK),
      ψ α (fst w) = fst (e (α (e.symm w))) := by
    intro α w
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, firstCoordAction_apply_fst,
      MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hinn : (MulAut.conj : P →* MulAut P).range ≤ ψ.ker := by
    rintro _ ⟨p, rfl⟩
    rw [MonoidHom.mem_ker]
    ext x
    obtain ⟨w, rfl⟩ := exists_fst_eq (hK := hK) x
    rw [hψapp, Equiv.Perm.one_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply, fst_mul, fst_mul, fst_inv]
    linear_combination fst (e p) * h2
  set ψbar := QuotientGroup.lift _ ψ hinn with hψbar
  have hψbar_mk : ∀ α : MulAut P, ψbar (α : MulAut P ⧸ (MulAut.conj : P →* MulAut P).range) =
      ψ α := fun α => QuotientGroup.lift_mk _ _ _
  have hker : ∀ q, ψbar q = 1 → q ^ 2 = 1 := by
    intro q hq
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hψbar_mk] at hq
    have hJ : MulAut.congr e α ∈ firstCoordFixing hK := by
      rw [← ker_firstCoordAction, MonoidHom.mem_ker]
      exact hq
    have hsq := mul_self_eq_one_of_mem_firstCoordFixing hJ
    rw [← map_mul, map_eq_one_iff _ (MulAut.congr e).injective] at hsq
    rw [← QuotientGroup.mk_pow, pow_two, hsq, QuotientGroup.mk_one]
  have hsemi : ∀ q, ∃ (c : Kˣ) (j : Fin 4), ∀ x, ψbar q x = c * x ^ 2 ^ (j : ℕ) := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hψbar_mk]
    exact (mem_range_firstCoordAction_iff _).mp ⟨_, rfl⟩
  have hoddH : ∀ h : H, Odd (orderOf (h : MulAut P ⧸ (MulAut.conj : P →* MulAut P).range)) := by
    intro h
    rw [Subgroup.orderOf_coe]
    exact hH.of_dvd_nat (orderOf_dvd_natCard h)
  have hscalar : ∀ h : H, ∀ x, ψbar h x = ψbar h 1 * x := by
    intro h x
    obtain ⟨c, j, hcj⟩ := hsemi h
    have hj : j = 0 := semilinear_eq_zero_of_odd_orderOf hK _ c j hcj
      ((hoddH h).of_dvd_nat (orderOf_map_dvd ψbar _))
    subst hj
    rw [hcj, hcj]
    simp
  have hne : ∀ h : H, ψbar h 1 ≠ 0 := by
    intro h h0
    have h1 : ψbar h 0 = 0 := by rw [hscalar h 0, mul_zero]
    exact one_ne_zero ((ψbar h).injective (h0.trans h1.symm))
  let χ : H →* Kˣ :=
    { toFun := fun h => Units.mk0 (ψbar h 1) (hne h)
      map_one' := Units.ext (by
        change ψbar ((1 : H) : MulAut P ⧸ (MulAut.conj : P →* MulAut P).range) 1 = 1
        rw [Subgroup.coe_one, ψbar.map_one]
        rfl)
      map_mul' := fun h h' => Units.ext (by
        change ψbar ((h * h' : H) : MulAut P ⧸ (MulAut.conj : P →* MulAut P).range) 1 =
          ψbar h 1 * ψbar h' 1
        rw [Subgroup.coe_mul, map_mul, Equiv.Perm.mul_apply, hscalar h]) }
  have hχ : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have h1 : ψbar h 1 = 1 := congrArg Units.val hh
    have hid : ψbar h = 1 :=
      Equiv.ext fun x => by rw [hscalar h, h1, one_mul, Equiv.Perm.one_apply]
    have hdvd : orderOf (h : MulAut P ⧸ (MulAut.conj : P →* MulAut P).range) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (hker _ hid)
    have hodd := hoddH h
    have hone : orderOf (h : MulAut P ⧸ (MulAut.conj : P →* MulAut P).range) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
      · exact h'
      · rw [h'] at hodd
        exact absurd hodd (Nat.not_odd_iff_even.mpr even_two)
    rw [orderOf_eq_one_iff] at hone
    exact Subtype.ext hone
  refine ⟨isCyclic_of_injective χ hχ, ?_⟩
  have := Subgroup.card_dvd_of_injective χ hχ
  rwa [Nat.card_units, hK] at this

theorem firstCoordAction_congr_conj {P : Type*} [Group P] (e : P ≃* unitaryFourW K hK) (p : P) :
    firstCoordAction hK (MulAut.congr e (MulAut.conj p)) = 1 := by
  have := charP_two_of_natCard_eq_sixteen hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext x
  obtain ⟨w, rfl⟩ := exists_fst_eq (hK := hK) x
  rw [firstCoordAction_apply_fst, Equiv.Perm.one_apply, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.apply_symm_apply, fst_mul, fst_mul, fst_inv]
  linear_combination fst (e p) * h2

theorem fst_eq_zero_of_outer_order_five {P : Type*} [Group P] (e : P ≃* unitaryFourW K hK)
    (α : MulAut P) (h5 : α ^ 5 ∈ (MulAut.conj : P →* MulAut P).range)
    (h1 : α ∉ (MulAut.conj : P →* MulAut P).range) (x : P)
    (hx : fst (e (α x)) = fst (e x)) : fst (e x) = 0 := by
  have := charP_two_of_natCard_eq_sixteen hK
  have hinner : ∀ γ ∈ (MulAut.conj : P →* MulAut P).range,
      firstCoordAction hK (MulAut.congr e γ) = 1 := by
    rintro _ ⟨p, rfl⟩
    exact firstCoordAction_congr_conj e p
  set σ := firstCoordAction hK (MulAut.congr e α) with hσ
  have hσ5 : σ ^ 5 = 1 := by
    rw [hσ, ← map_pow, ← map_pow]
    exact hinner _ h5
  have hσ1 : σ ≠ 1 := by
    intro h
    have hJ : MulAut.congr e α ∈ firstCoordFixing hK := by
      rw [← ker_firstCoordAction, MonoidHom.mem_ker]
      exact h
    have hsq := mul_self_eq_one_of_mem_firstCoordFixing hJ
    rw [← map_mul, map_eq_one_iff _ (MulAut.congr e).injective] at hsq
    apply h1
    have hα : α = α ^ 5 := by
      rw [show α ^ 5 = α * (α * α) * (α * α) by simp [pow_succ, mul_assoc], hsq, mul_one,
        mul_one]
    rw [hα]
    exact h5
  obtain ⟨c, j, hcj⟩ := (mem_range_firstCoordAction_iff σ).mp ⟨_, rfl⟩
  have hodd : Odd (orderOf σ) := by
    have hdvd : orderOf σ ∣ 5 := orderOf_dvd_of_pow_eq_one hσ5
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h <;> rw [h] <;> decide
  have hj := semilinear_eq_zero_of_odd_orderOf hK σ c j hcj hodd
  subst hj
  have hc1 : (c : K) ≠ 1 := by
    intro hc
    apply hσ1
    ext y
    rw [hcj, hc]
    simp
  have hσx : σ (fst (e x)) = fst (e (α x)) := by
    rw [hσ, firstCoordAction_apply_fst, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hcj, hx] at hσx
  simp only [Fin.val_zero, pow_zero, pow_one] at hσx
  have hprod : ((c : K) - 1) * fst (e x) = 0 := by linear_combination hσx
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd (sub_eq_zero.mp h) hc1
  · exact h


end

end CFSG.LyonsUnitaryFour
