module

public import CFSG.CGT.Stroth77.StrothSection2Proof
public import CFSG.CGT.Stroth77.TorusNormalForm

public section

namespace CFSG.CGT.Stroth77

variable {G : Type*} [Group G] [Finite G] {X : StrothAmbient G}

theorem mem_omega_iff_of_comm {i : ℕ} {M : Type*} [Group M]
    (hcomm : ∀ a b : M, a * b = b * a) {y : M} :
    y ∈ CFSG.omega M (p := 2) i ↔ y ^ (2 ^ i) = 1 := by
  constructor
  · intro hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => simpa using hx
    | one => simp
    | mul x z _ _ hx hz =>
        have hc : Commute x z := hcomm x z
        rw [hc.mul_pow, hx, hz, one_mul]
    | inv x _ hx => rw [inv_pow, hx, inv_one]
  · intro hy
    exact Subgroup.subset_closure (by simpa using hy)

theorem mem_omegaIn_of_pow_eq_one {i : ℕ} {D : Subgroup G} {x : G} (hx : x ∈ D)
    (h : x ^ (2 ^ i) = 1) : x ∈ omegaIn i D := by
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  exact Subgroup.subset_closure (Subtype.ext h)

theorem four_nsmul_eq_zero_of_k_le_two {k : Fin 3 → ℕ} (hk : ∀ i, k i ≤ 2)
    (v : Torus k) : (4 : ℕ) • v = 0 := by
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]
  have hdvd : 2 ^ k i ∣ 4 := by
    have h := pow_dvd_pow (2 : ℕ) (hk i)
    norm_num at h ⊢
    exact h
  have hzero : (4 : ZMod (2 ^ k i)) = 0 :=
    (ZMod.natCast_eq_zero_iff 4 (2 ^ k i)).mpr hdvd
  change (4 : ZMod (2 ^ k i)) * v i = 0
  rw [hzero, zero_mul]

theorem mem_omegaIn_iff_of_comm {i : ℕ} {D : Subgroup G}
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {x : G} :
    x ∈ omegaIn i D ↔ x ∈ D ∧ x ^ (2 ^ i) = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hcommD : ∀ a b : D, a * b = b * a := fun a b =>
      Subtype.ext (hcomm a a.2 b b.2)
    have hy' : (y : D) ^ (2 ^ i) = 1 := (mem_omega_iff_of_comm hcommD).mp hy
    exact ⟨y.2, by simpa using congrArg Subtype.val hy'⟩
  · rintro ⟨hxD, hx⟩
    exact mem_omegaIn_of_pow_eq_one hxD hx


theorem card_omegaIn_two_eq {D : Subgroup G} {k : Fin 3 → ℕ}
    (e : Additive D ≃+ Torus k) :
    Nat.card (omegaIn 2 D) = Nat.card {v : Torus k // (4 : ℤ) • v = 0} := by
  have hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => by
    have h := e.injective
      (show e (Additive.ofMul (⟨a, ha⟩ * ⟨b, hb⟩)) =
        e (Additive.ofMul (⟨b, hb⟩ * ⟨a, ha⟩)) by
        rw [ofMul_mul, ofMul_mul, map_add, map_add, add_comm])
    exact congrArg Subtype.val (Additive.ofMul.injective h)
  refine Nat.card_congr
    { toFun := fun x =>
        ⟨e (Additive.ofMul ⟨x.1, omegaIn_le 2 D x.2⟩), ?_⟩
      invFun := fun v => ⟨((Additive.toMul (e.symm v.1) : D) : G), ?_⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  · have hx4 : (⟨x.1, omegaIn_le 2 D x.2⟩ : D) ^ 4 = 1 := by
      have h := (mem_omegaIn_iff_of_comm hD).mp x.2
      exact Subtype.ext (by simpa using h.2)
    calc (4 : ℤ) • e (Additive.ofMul ⟨x.1, omegaIn_le 2 D x.2⟩)
        = e ((4 : ℤ) • Additive.ofMul ⟨x.1, omegaIn_le 2 D x.2⟩) :=
          (map_zsmul e 4 _).symm
      _ = e (Additive.ofMul ((⟨x.1, omegaIn_le 2 D x.2⟩ : D) ^ 4)) := by
          rw [ofMul_pow]
          norm_num
      _ = 0 := by rw [hx4]; simp
  · have h1 : (Additive.toMul (e.symm v.1) : D) ^ 4 = 1 := by
      apply Additive.ofMul.injective
      apply e.injective
      rw [ofMul_pow, map_nsmul, ofMul_toMul, AddEquiv.apply_symm_apply]
      rw [← natCast_zsmul]
      have h4 : ((4 : ℕ) : ℤ) • v.1 = 0 := by simpa using v.2
      rw [h4]
      simp
    exact mem_omegaIn_of_pow_eq_one (Additive.toMul (e.symm v.1)).2
      (by simpa using congrArg Subtype.val h1)

theorem card_four_torsion_torus (k : Fin 3 → ℕ) :
    Nat.card {v : Torus k // (4 : ℤ) • v = 0} =
      ∏ i, Nat.card {z : ZMod (2 ^ k i) // (4 : ℤ) • z = 0} := by
  have e : {v : Torus k // (4 : ℤ) • v = 0} ≃
      ∀ i, {z : ZMod (2 ^ k i) // (4 : ℤ) • z = 0} :=
    (Equiv.subtypeEquivRight fun v => by
      rw [funext_iff]; simp only [Pi.smul_apply, Pi.zero_apply]).trans
      Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_pi]

theorem card_four_torsion_torus_133 :
    Nat.card {v : Torus ![1, 3, 3] // (4 : ℤ) • v = 0} = 32 := by
  rw [card_four_torsion_torus, Fin.prod_univ_three]
  simp only [Nat.card_eq_fintype_card]
  decide


theorem pow_four_eq_one_of_dataA {x : G} (hx : x ∈ X.A) : x ^ 4 = 1 := by
  have h4 : (4 : ℕ) • X.dataA.e (Additive.ofMul ⟨x, hx⟩) = 0 :=
    four_nsmul_eq_zero_of_k_le_two
      (k := (StrothTypeIndex.t100 1).k)
      (by intro i; fin_cases i <;> decide) _
  have h : (⟨x, hx⟩ : X.A) ^ 4 = 1 := by
    apply Additive.ofMul.injective
    apply X.dataA.e.injective
    rw [ofMul_pow, map_nsmul, h4, ofMul_one, map_zero]
  simpa using congrArg Subtype.val h

theorem A_le_omegaIn_two (Z : StrothDatum X) : X.A ≤ omegaIn 2 Z.D := by
  intro x hx
  exact mem_omegaIn_of_pow_eq_one (Z.hAD hx) (pow_four_eq_one_of_dataA hx)


theorem omegaIn_two_le_mhoOne_of_three_le_k (Z : StrothDatum X)
    (hk : ∀ i, 3 ≤ Z.τ.k i) : omegaIn 2 Z.D ≤ mhoOne Z.D := by
  have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  intro x hx
  obtain ⟨hxD, hx4⟩ := (mem_omegaIn_iff_of_comm hcomm).mp hx
  set v : Torus Z.τ.k := Z.dataD.e (Additive.ofMul ⟨x, hxD⟩) with hv
  have hv4 : (4 : ℤ) • v = 0 := by
    calc (4 : ℤ) • v
        = Z.dataD.e ((4 : ℤ) • Additive.ofMul (⟨x, hxD⟩ : Z.D)) := by
          rw [hv, map_zsmul]
      _ = Z.dataD.e (Additive.ofMul ((⟨x, hxD⟩ : Z.D) ^ 4)) := by
          rw [ofMul_pow]
          norm_num
      _ = Z.dataD.e (Additive.ofMul (1 : Z.D)) := by
          rw [show (⟨x, hxD⟩ : Z.D) ^ 4 = 1 from Subtype.ext hx4]
      _ = 0 := by simp
  obtain ⟨V, hV⟩ : ∃ V : Fin 3 → ℤ, v = Torus.ofInt Z.τ.k V := by
    choose V hV using fun i => ZMod.intCast_surjective (v i)
    exact ⟨V, funext fun i => by simpa [Torus.ofInt_apply] using (hV i).symm⟩
  have hdiv : ∀ i, ((2 ^ Z.τ.k i : ℕ) : ℤ) ∣ 4 * V i := by
    intro i
    have hi : ((4 * V i : ℤ) : ZMod (2 ^ Z.τ.k i)) = 0 := by
      have h := congrFun (hV ▸ hv4) i
      simpa only [Torus.ofInt_apply, Pi.smul_apply, Pi.zero_apply, zsmul_eq_mul,
        Int.cast_ofNat, Int.cast_mul, Int.cast_natCast] using h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (4 * V i) (2 ^ Z.τ.k i)).mp hi
  have hEven : ∀ i, Even (V i) := by
    intro i
    have h8 : (8 : ℤ) ∣ ((2 ^ Z.τ.k i : ℕ) : ℤ) := by
      have h := pow_dvd_pow (2 : ℕ) (hk i)
      exact_mod_cast h
    have h8dvd : (8 : ℤ) ∣ 4 * V i := h8.trans (hdiv i)
    obtain ⟨t, ht⟩ := h8dvd
    refine ⟨t, ?_⟩
    have h4 : 4 * V i = 4 * (2 * t) := by rw [ht]; ring
    linarith
  obtain ⟨w, hw⟩ := (Torus.exists_two_zsmul_eq_iff
    (fun i => le_trans (by norm_num : 1 ≤ 3) (hk i)) V).mpr hEven
  have hwv : (2 : ℤ) • w = v := by rw [hV]; exact hw
  set y : Z.D := Additive.toMul (Z.dataD.e.symm w) with hy
  have hy2 : (y : G) * (y : G) = x := by
    have hy2' : y * y = ⟨x, hxD⟩ := by
      apply Additive.ofMul.injective
      apply Z.dataD.e.injective
      have hyw : Additive.ofMul y = Z.dataD.e.symm w := by
        rw [hy]
        simp
      have h1 : Z.dataD.e (Additive.ofMul (y * y)) = w + w := by
        rw [ofMul_mul, map_add, hyw]
        simp
      rw [h1]
      show w + w = v
      rw [← hwv, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, natCast_zsmul, two_nsmul]
    exact congrArg Subtype.val hy2'
  rw [← hy2]
  simpa [pow_two] using
    CFSG.GroupTheory.HuppertProduct.pow_mem_mho (S := Z.D) (n := 2) y.2

theorem A_le_mhoOne_of_three_le_k (Z : StrothDatum X) (hk : ∀ i, 3 ≤ Z.τ.k i) :
    X.A ≤ mhoOne Z.D :=
  (A_le_omegaIn_two Z).trans (omegaIn_two_le_mhoOne_of_three_le_k Z hk)


end CFSG.CGT.Stroth77
