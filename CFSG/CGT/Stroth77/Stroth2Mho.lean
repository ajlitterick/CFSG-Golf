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


end CFSG.CGT.Stroth77
