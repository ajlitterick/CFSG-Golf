module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutBlocks
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Chart
public import CFSG.ClassicalInvolution.Phan.Center

public section

namespace CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalInvolution.Models

section Sign

@[expose] def signVal (K : Type) [Field K] (b : ZMod 2) : K := if b = 0 then 1 else -1

theorem signVal_mul_self {K : Type} [Field K] (b : ZMod 2) : signVal K b * signVal K b = 1 := by
  unfold signVal
  split_ifs <;> simp

theorem signVal_mul_signVal_of_ne {K : Type} [Field K] {b c : ZMod 2} (h : b ≠ c) :
    signVal K b * signVal K c = -1 := by
  have hb : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  unfold signVal
  rcases hb b with rfl | rfl <;> rcases hb c with rfl | rfl <;> simp_all

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def negOneN : normOne (unitaryInvolution K p f) :=
  ⟨-1, (mem_normOne _).2 (by simp)⟩

@[expose] noncomputable def signN (b : ZMod 2) : normOne (unitaryInvolution K p f) :=
  if b = 0 then 1 else negOneN

theorem coe_signN (b : ZMod 2) :
    (((signN b : normOne (unitaryInvolution K p f)) : Kˣ) : K) = signVal K b := by
  unfold signN signVal
  split_ifs <;> simp [negOneN]

theorem coe_signN_inv (b : ZMod 2) :
    ((((signN b : normOne (unitaryInvolution K p f)) : Kˣ)⁻¹ : Kˣ) : K) = signVal K b := by
  unfold signN signVal
  split_ifs <;> simp [negOneN]

@[expose] noncomputable def conjSign (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (v : Fin n → ZMod 2) :
    Su K p f n →* Su K p f n :=
  conjDiag hK fun i => signN (v i)

theorem coe_coe_conjSign_apply (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (v : Fin n → ZMod 2)
    (x : Su K p f n) (a b : Fin n) :
    (((conjSign hK v x : Su K p f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
      signVal K (v a) * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b * signVal K (v b) := by
  rw [conjSign, coe_conjDiag_apply, coe_signN, coe_signN_inv]

end Sign

section Coordinate

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem mem_LcU_iff {T : Pair n} {x : Su K p f n} :
    x ∈ LcU K p f T ↔ suMat x * zMat K n T.1 = zMat K n T.1 * suMat x ∧
      suMat x * (1 + zMat K n T.1) = 1 + zMat K n T.1 :=
  Iff.rfl

theorem LcU_entry (h2 : (2 : K) ≠ 0) {T : Pair n} {x : Su K p f n} (hx : x ∈ LcU K p f T)
    (a b : Fin n) (hab : ¬ (a ∈ T.1 ∧ b ∈ T.1)) :
    suMat x a b = if a = b then 1 else 0 := by
  obtain ⟨h1, h3⟩ := mem_LcU_iff.mp hx
  have e1 := congrFun (congrFun h1 a) b
  have e3 := congrFun (congrFun h3 a) b
  simp only [zMat, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_add, Matrix.mul_one,
    Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply] at e1 e3
  by_cases hb : b ∈ T.1
  · have ha : a ∉ T.1 := fun ha => hab ⟨ha, hb⟩
    have hne : a ≠ b := fun h => ha (h ▸ hb)
    simp only [hb, ha, ite_true, ite_false] at e1
    simp only [hne, ite_false]
    have : (2 : K) * suMat x a b = 0 := by linear_combination -e1
    exact (mul_eq_zero.mp this).resolve_left h2
  · by_cases hab' : a = b
    · subst hab'
      simp only [hb, ite_false, ite_true] at e3 ⊢
      have : (2 : K) * suMat x a a = 2 * 1 := by linear_combination e3
      exact mul_left_cancel₀ h2 this
    · simp only [hb, ite_false, hab'] at e3 ⊢
      have : (2 : K) * suMat x a b = 0 := by linear_combination e3
      exact (mul_eq_zero.mp this).resolve_left h2

theorem conjSign_mem_LcU (hK : Nat.card K = (p ^ f) ^ 2) (v : Fin n → ZMod 2) {T : Pair n}
    {x : Su K p f n} (hx : x ∈ LcU K p f T) : conjSign hK v x ∈ LcU K p f T := by
  obtain ⟨h1, h3⟩ := mem_LcU_iff.mp hx
  refine mem_LcU_iff.mpr ⟨Matrix.ext fun a b => ?_, Matrix.ext fun a b => ?_⟩
  · have e1 := congrFun (congrFun h1 a) b
    simp only [suMat, zMat, Matrix.mul_diagonal, Matrix.diagonal_mul,
      coe_coe_conjSign_apply] at e1 ⊢
    linear_combination (signVal K (v a) * signVal K (v b)) * e1
  · have e3 := congrFun (congrFun h3 a) b
    simp only [suMat, zMat, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.one_apply, Matrix.diagonal_apply, coe_coe_conjSign_apply] at e3 ⊢
    by_cases hab : a = b
    · subst hab
      simp only [ite_true] at e3 ⊢
      have := signVal_mul_self (K := K) (v a)
      linear_combination (signVal K (v a) * signVal K (v a)) * e3 +
        (1 + (if a ∈ T.1 then -1 else 1)) * this
    · simp only [hab, ite_false] at e3 ⊢
      linear_combination (signVal K (v a) * signVal K (v b)) * e3

theorem conjSign_eq_of_const (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (v : Fin n → ZMod 2) {T : Pair n} (hv : ∀ a ∈ T.1, ∀ b ∈ T.1, v a = v b)
    {x : Su K p f n} (hx : x ∈ LcU K p f T) : conjSign hK v x = x := by
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => ?_))
  have := coe_coe_conjSign_apply hK v x a b
  rw [this]
  by_cases hab : a ∈ T.1 ∧ b ∈ T.1
  · rw [hv a hab.1 b hab.2]
    change signVal K (v b) * suMat x a b * signVal K (v b) = suMat x a b
    linear_combination (suMat x a b) * signVal_mul_self (K := K) (v b)
  · have := LcU_entry h2 hx a b hab
    change signVal K (v a) * suMat x a b * signVal K (v b) = suMat x a b
    rw [this]
    by_cases hab' : a = b
    · subst hab'
      simp only [ite_true]
      linear_combination signVal_mul_self (K := K) (v a)
    · simp [hab']

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem unitSignedSwapMatrix_apply' {i j : Fin n} (a b : Fin n) :
    (unitSignedSwapMatrix i j : Matrix (Fin n) (Fin n) K) a b =
      if Equiv.swap i j a = b then (if a = i then -1 else 1) else 0 := by
  rw [unitSignedSwapMatrix, Matrix.diagonal_mul]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem swap_zdiag_eq {i j : Fin n} (a b : Fin n) (hab : Equiv.swap i j a = b) :
    (if b ∈ ({i, j} : Finset (Fin n)) then (-1 : K) else 1) =
      (if a ∈ ({i, j} : Finset (Fin n)) then (-1 : K) else 1) := by
  subst hab
  by_cases h1 : a = i
  · subst h1; simp
  · by_cases h3 : a = j
    · subst h3; simp
    · simp [Equiv.swap_apply_of_ne_of_ne h1 h3, h1, h3]

theorem exists_swap_mem_LcU (hK : Nat.card K = (p ^ f) ^ 2) (h : UnitaryFieldData p f K)
    {T : Pair n} {i j : Fin n} (hij : i ≠ j) (hT : T.1 = {i, j}) :
    ∃ x ∈ LcU K p f T, ∀ v : Fin n → ZMod 2, v i ≠ v j →
      conjSign hK v x = zEltU K p f T * x := by
  obtain ⟨M, hM, hMmem⟩ := unitSignedSwapMatrix_mem (E := K) (m := n) h hij
  have hMSU : M ∈ SUid (unitaryInvolution K p f) n := by
    have : M ∈ unitarySU p f K n := by rw [unitarySU_eq_gramSU h]; exact hMmem
    rw [SUid_eq_statedSU hK n]
    exact this
  have hxe : ∀ a b, suMat (⟨M, hMSU⟩ : Su K p f n) a b =
      if Equiv.swap i j a = b then (if a = i then -1 else 1) else 0 := fun a b => by
    change (M : Matrix (Fin n) (Fin n) K) a b = _
    rw [hM, unitSignedSwapMatrix_apply']
  refine ⟨⟨M, hMSU⟩, ?_, fun v hv => ?_⟩
  · rw [mem_LcU_iff, hT]
    refine ⟨Matrix.ext fun a b => ?_, Matrix.ext fun a b => ?_⟩
    · simp only [zMat, Matrix.mul_diagonal, Matrix.diagonal_mul, hxe]
      by_cases hab : Equiv.swap i j a = b
      · rw [ite_eq_left hab, swap_zdiag_eq a b hab, mul_comm]
      · simp [hab]
    · simp only [zMat, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_diagonal,
        Matrix.one_apply, Matrix.diagonal_apply, hxe]
      by_cases hab : Equiv.swap i j a = b
      · rw [ite_eq_left hab, swap_zdiag_eq a b hab]
        by_cases ha : a ∈ ({i, j} : Finset (Fin n))
        · have hne : a ≠ b := by
            rw [← hab]
            rcases Finset.mem_insert.mp ha with rfl | ha'
            · simp [hij]
            · rw [Finset.mem_singleton] at ha'
              subst ha'
              simp [hij.symm]
          simp [ha, hne]
        · have hb : b = a := by
            rw [← hab]
            exact Equiv.swap_apply_of_ne_of_ne (fun h' => ha (by simp [h']))
              (fun h' => ha (by simp [h']))
          subst hb
          have hai : b ≠ i := fun h' => ha (by simp [h'])
          simp [ha, hai]
      · rw [ite_eq_right hab]
        by_cases hab' : a = b
        · subst hab'
          have ha : a ∈ ({i, j} : Finset (Fin n)) := by
            by_contra ha
            exact hab (Equiv.swap_apply_of_ne_of_ne (fun h' => ha (by simp [h']))
              (fun h' => ha (by simp [h'])))
          simp [ha]
        · simp [hab']
  · refine Subtype.ext (Units.ext (Matrix.ext fun a b => ?_))
    rw [coe_coe_conjSign_apply]
    change signVal K (v a) * suMat (⟨M, hMSU⟩ : Su K p f n) a b * signVal K (v b) =
      suMat (zEltU K p f T * (⟨M, hMSU⟩ : Su K p f n)) a b
    rw [suMat_mul, suMat_zEltU, hT]
    simp only [zMat, Matrix.diagonal_mul, hxe]
    by_cases hab : Equiv.swap i j a = b
    · rw [ite_eq_left hab]
      by_cases ha : a ∈ ({i, j} : Finset (Fin n))
      · rcases Finset.mem_insert.mp ha with rfl | ha'
        · have hb : b = j := by rw [← hab]; simp
          subst hb
          rw [ite_eq_left ha]
          have := signVal_mul_signVal_of_ne (K := K) hv
          simp only [ite_true]
          linear_combination (-1 : K) * this
        · rw [Finset.mem_singleton] at ha'
          subst ha'
          have hb : b = i := by rw [← hab]; simp
          subst hb
          rw [ite_eq_left ha]
          have := signVal_mul_signVal_of_ne (K := K) hv.symm
          simp [hij.symm]
          linear_combination this
      · have hai : a ≠ i := fun h' => ha (by simp [h'])
        have haj : a ≠ j := fun h' => ha (by simp [h'])
        have hb : b = a := by
          rw [← hab]
          exact Equiv.swap_apply_of_ne_of_ne hai haj
        subst hb
        rw [ite_eq_right ha]
        simp only [hai, ite_false]
        linear_combination (signVal_mul_self (K := K) (v b))
    · simp [hab]

end Coordinate

section Helpers

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_normOne_ne (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    ∃ u : normOne (unitaryInvolution K p f), ((u : Kˣ) : K) ≠ 1 ∧
      (((u : Kˣ)⁻¹ : Kˣ) : K) ≠ ((u : Kˣ) : K) := by
  obtain ⟨c, hcN, hck⟩ := exists_norm_one_not_fixed h hp2
  have hbar : ∀ x, h.bar x = unitaryInvolution K p f x := fun x => by
    rw [UnitaryFieldData.bar_apply, unitaryInvolution_apply]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcN
    exact zero_ne_one hcN
  have hcσ : unitaryInvolution K p f c * c = 1 := by rw [← hbar]; exact hcN
  refine ⟨⟨Units.mk0 c hc0, (mem_normOne _).2 (by simpa using hcσ)⟩, ?_, ?_⟩
  · intro h1
    exact hck (by simp only [Units.val_mk0] at h1; rw [h1]; exact one_mem _)
  · intro h1
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0] at h1
    apply hck
    have h3 : c * c = 1 := by
      calc c * c = c * c⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel₀ hc0
    rcases mul_self_eq_one_iff.mp h3 with h4 | h4
    · rw [h4]; exact one_mem _
    · rw [h4]; exact neg_mem (one_mem _)

theorem lift_matrix_of_fixed (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) {Y : Type}
    [Group Y] {θ : Su K p f n →* Y} (hker : θ.ker ≤ Subgroup.center (Su K p f n)) {σ : Y ≃* Y}
    {α : Su K p f n →* Su K p f n} (hα : ∀ x, θ (α x) = σ (θ x)) {x : Su K p f n}
    (hx : σ (θ x) = θ x) :
    ∃ u : Kˣ, suMat (α x) = (u : K) • suMat x := by
  have hz : x⁻¹ * α x ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hx, inv_mul_cancel]
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) hn (hker hz)
  refine ⟨u, ?_⟩
  have h1 : α x = x * (x⁻¹ * α x) := by group
  have h2 : suMat (α x) = suMat x * Matrix.scalar (Fin n) (u : K) := by
    rw [h1]
    rw [suMat_mul]
    exact congrArg (suMat x * ·) hu
  rw [h2, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

end Helpers

section EntryCases

variable {K : Type} [Field K]

theorem torus_entry_cases_id {m : ℕ} (a : Fin m) (u : K) (hu1 : u ≠ 1) (hu2 : u⁻¹ ≠ u)
    (i j : Fin (m + 1)) (x : K) (hx : x ≠ 0)
    (h : (if i.val = a.val then u else if i.val = a.val + 1 then u⁻¹ else 1) * x =
      x * (if j.val = a.val then u else if j.val = a.val + 1 then u⁻¹ else 1)) :
    i = j ∨ (i.val ≠ a.val ∧ i.val ≠ a.val + 1 ∧ j.val ≠ a.val ∧ j.val ≠ a.val + 1) := by
  have h' : (if i.val = a.val then u else if i.val = a.val + 1 then u⁻¹ else 1) =
      (if j.val = a.val then u else if j.val = a.val + 1 then u⁻¹ else 1) := by
    apply mul_right_cancel₀ hx
    rw [h, mul_comm]
  have hi : i.val = a.val ∨ i.val = a.val + 1 ∨ (i.val ≠ a.val ∧ i.val ≠ a.val + 1) := by omega
  have hj : j.val = a.val ∨ j.val = a.val + 1 ∨ (j.val ≠ a.val ∧ j.val ≠ a.val + 1) := by omega
  have hu1' : u⁻¹ ≠ 1 := fun h0 => hu1 (by simpa using h0)
  rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj
  · exact Or.inl (Fin.ext (by omega))
  · simp [hi, hj] at h'
    exact absurd h' hu2.symm
  · simp [hi, hj.1, hj.2, hu1] at h'
  · simp [hi, hj] at h'
    exact absurd h' hu2
  · exact Or.inl (Fin.ext (by omega))
  · simp [hi, hj.1, hj.2, hu1'] at h'
  · simp [hi.1, hi.2, hj] at h'
    exact absurd h' hu1.symm
  · simp [hi.1, hi.2, hj] at h'
    exact absurd h' hu1
  · exact Or.inr ⟨hi.1, hi.2, hj.1, hj.2⟩

end EntryCases

section Diagonal

variable {K : Type} [Field K]


end Diagonal

section Tail

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]


end Tail

section Pattern

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]


end Pattern

section Roots

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] def charOfU {n : ℕ} (v : Fin n → ZMod 2) (T : Pair n) : ZMod 2 := ∑ i ∈ T.1, v i

theorem charOfU_eq_zero_iff {n : ℕ} (v : Fin n → ZMod 2) {T : Pair n} {i j : Fin n} (hij : i ≠ j)
    (hT : T.1 = {i, j}) : charOfU v T = 0 ↔ v i = v j := by
  unfold charOfU
  rw [hT, Finset.sum_pair hij]
  have hb : ∀ b : ZMod 2, b + b = 0 := by decide
  constructor
  · intro h
    have h1 : v i = -v j := eq_neg_of_add_eq_zero_left h
    rw [h1]
    have : ∀ b : ZMod 2, -b = b := by decide
    exact this _
  · intro h
    rw [h]
    exact hb _

theorem conjSign_conjSign (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (v : Fin n → ZMod 2)
    (x : Su K p f n) : conjSign hK v (conjSign hK v x) = x := by
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => ?_))
  rw [coe_coe_conjSign_apply, coe_coe_conjSign_apply]
  linear_combination (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b * signVal K (v b) *
      signVal K (v b)) * signVal_mul_self (K := K) (v a) +
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b * signVal_mul_self (K := K) (v b)

theorem zEltU_not_mem_center (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0) {n : ℕ}
    (hn : 3 ≤ n) (T : Pair n) : zEltU K p f T ∉ Subgroup.center (Su K p f n) := by
  intro hz
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) hn hz
  have hcard := T.2
  obtain ⟨i, hi⟩ : ∃ i, i ∈ T.1 := Finset.card_pos.mp (by omega)
  obtain ⟨r, hr⟩ : ∃ r, r ∉ T.1 := by
    by_contra hall
    push Not at hall
    have : T.1 = Finset.univ := Finset.eq_univ_of_forall hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have e1 : zMat K n T.1 i i = (u : K) := by
    have := congrFun (congrFun hu i) i
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
    exact this
  have e2 : zMat K n T.1 r r = (u : K) := by
    have := congrFun (congrFun hu r) r
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
    exact this
  rw [zMat_apply_self, ite_eq_left hi] at e1
  rw [zMat_apply_self, ite_eq_right hr] at e2
  exact h2 (by linear_combination e2 - e1)

theorem root_pattern (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hn : 3 ≤ n) {Y : Type} [Group Y] (θ : Su K p f n →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f n)) (σ : Y ≃* Y) (v : Fin n → ZMod 2)
    (hv : ∀ x, σ (θ x) = θ (conjSign hK v x)) (T : Pair n) :
    ((LcU K p f T).map θ).map σ.toMonoidHom = (LcU K p f T).map θ ∧
      ((∀ x ∈ LcU K p f T, σ (θ x) = θ x) ↔ charOfU v T = 0) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨conjSign hK v x, conjSign_mem_LcU hK v hx, (hv x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨θ (conjSign hK v x), ⟨conjSign hK v x, conjSign_mem_LcU hK v hx, rfl⟩, ?_⟩
      change σ (θ (conjSign hK v x)) = θ x
      rw [hv, conjSign_conjSign]
  · obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp T.2
    rw [charOfU_eq_zero_iff v hij hT]
    constructor
    · intro hfix
      by_contra hne
      obtain ⟨x, hxL, hxc⟩ := exists_swap_mem_LcU hK h hij hT
      have h1 := hfix x hxL
      rw [hv, hxc v hne, map_mul] at h1
      have h3 : θ (zEltU K p f T) = 1 :=
        mul_right_cancel (h1.trans (one_mul (θ x)).symm)
      exact zEltU_not_mem_center hK h2 hn T (hker (MonoidHom.mem_ker.mpr h3))
    · intro hvij x hx
      have hconst : ∀ a ∈ T.1, ∀ b ∈ T.1, v a = v b := by
        intro a ha b hb
        rw [hT] at ha hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
        · exact hvij
        · exact hvij.symm
      rw [hv, conjSign_eq_of_const hK h2 v hconst hx]

end Roots

section Main


end Main

end CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
