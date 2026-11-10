module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open scoped commutatorElement

variable {Y X : Type*} [Group Y] [Group X]

theorem commutatorElement_mul_central_left {k : Y} (hk : k ∈ Subgroup.center Y) (a b : Y) :
    ⁅a * k, b⁆ = ⁅a, b⁆ := by
  have h : k * b * k⁻¹ = b := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hk b).symm
  calc ⁅a * k, b⁆ = a * (k * b * k⁻¹) * a⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [h]; rfl

theorem commutatorElement_mul_central_right {k : Y} (hk : k ∈ Subgroup.center Y) (a b : Y) :
    ⁅a, b * k⁆ = ⁅a, b⁆ := by
  have h : k * a⁻¹ * k⁻¹ = a⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hk a⁻¹).symm
  calc ⁅a, b * k⁆ = a * b * (k * a⁻¹ * k⁻¹) * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [h]; rfl

theorem commutator_le_center_of_map_commute (π : Y →* X) (hker : π.ker ≤ Subgroup.center Y)
    {A B : Subgroup Y} (hc : ∀ a ∈ A, ∀ b ∈ B, π a * π b = π b * π a) :
    ⁅A, B⁆ ≤ Subgroup.center Y := by
  refine le_trans ?_ hker
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [MonoidHom.mem_ker, commutatorElement_def]
  simp only [map_mul, map_inv]
  rw [hc a ha b hb]
  group

theorem commutes_derived_left {A B : Subgroup Y} (h : ⁅A, B⁆ ≤ Subgroup.center Y) :
    ∀ α ∈ ⁅A, A⁆, ∀ w ∈ B, w * α = α * w := by
  have h1 : ⁅⁅A, B⁆, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (h.trans (Subgroup.center_le_centralizer _))
  have h2 : ⁅⁅B, A⁆, A⁆ = ⊥ := by
    rw [Subgroup.commutator_comm B A]; exact h1
  have h3 : ⁅⁅A, A⁆, B⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  intro α hα w hw
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3 hα)
    w hw


theorem commutator_pow_of_central' {x y : Y} (hc : ∀ k : ℕ, ⁅x ^ k, y⁆ ∈ Subgroup.center Y)
    (n : ℕ) : ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ⁅x ^ n * x, y⁆ = x ^ n * ⁅x, y⁆ * (x ^ n)⁻¹ * ⁅x ^ n, y⁆ := by
      simp only [commutatorElement_def]
      group
    have hx : ⁅x, y⁆ ∈ Subgroup.center Y := by simpa using hc 1
    have h2 : x ^ n * ⁅x, y⁆ * (x ^ n)⁻¹ = ⁅x, y⁆ := by
      rw [Subgroup.mem_center_iff.mp hx (x ^ n)]
      group
    rw [pow_succ, h1, h2, ih, pow_succ']

theorem commutes_of_map_commute_exponent3 (π : Y →* X) (hker : π.ker ≤ Subgroup.center Y)
    (hcop : ∀ n ∈ π.ker, ¬ 3 ∣ orderOf n) {A L : Subgroup Y}
    (hL : ∀ l ∈ L, l ^ 3 ∈ ⁅L, L⁆) (hc : ∀ a ∈ A, ∀ l ∈ L, π a * π l = π l * π a) :
    ∀ a ∈ A, ∀ l ∈ L, a * l = l * a := by
  have hAL : ⁅A, L⁆ ≤ Subgroup.center Y := commutator_le_center_of_map_commute π hker hc
  have hLA : ⁅L, A⁆ ≤ Subgroup.center Y := by rwa [Subgroup.commutator_comm]
  have hα := commutes_derived_left hLA
  intro a ha l hl
  have hcl : ∀ k : ℕ, ⁅l ^ k, a⁆ ∈ Subgroup.center Y := fun k =>
    hLA (Subgroup.commutator_mem_commutator (L.pow_mem hl k) ha)
  have hmem : ⁅l, a⁆ ∈ π.ker := by
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    rw [(hc a ha l hl).symm]
    group
  have hpow : ⁅l, a⁆ ^ 3 = 1 := by
    rw [← commutator_pow_of_central' hcl 3, commutatorElement_eq_one_iff_mul_comm]
    exact (hα (l ^ 3) (hL l hl) a ha).symm
  have hord : orderOf ⁅l, a⁆ ∣ 3 := orderOf_dvd_of_pow_eq_one hpow
  have h1 : orderOf ⁅l, a⁆ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
    · exact h
    · exact (hcop _ hmem (dvd_of_eq h.symm)).elim
  exact (commutatorElement_eq_one_iff_mul_comm.mp (orderOf_eq_one_iff.mp h1)).symm


theorem orderOf_coprime_six {O : Subgroup Y} (hodd : Odd (Nat.card O)) (h3 : ¬ 3 ∣ Nat.card O)
    {n : Y} (hn : n ∈ O) : Nat.Coprime (orderOf n) 6 := by
  have h2 : Nat.Coprime (Nat.card O) 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have h3' : Nat.Coprime (Nat.card O) 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact h3
  have hc6 : Nat.Coprime (Nat.card O) 6 := by
    simpa using Nat.Coprime.mul_right h2 h3'
  exact Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard O hn) hc6

theorem le_of_map_le_of_exponent (π : Y →* X) (hker : π.ker ≤ Subgroup.center Y)
    (hcop : ∀ n ∈ π.ker, Nat.Coprime (orderOf n) 6) {L₁ L₂ : Subgroup Y}
    (h₁ : ∀ l ∈ L₁, l ^ 12 = 1) (h₂ : ∀ l ∈ L₂, l ^ 12 = 1)
    (h : ∀ l ∈ L₁, π l ∈ L₂.map π) : L₁ ≤ L₂ := by
  intro l hl
  obtain ⟨l₂, hl₂, hll₂⟩ := h l hl
  have hn : l₂⁻¹ * l ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul π l₂⁻¹ l, map_inv, hll₂, inv_mul_cancel]
  have hnc := Subgroup.mem_center_iff.mp (hker hn)
  have hcomm : Commute l₂⁻¹ l := by
    show l₂⁻¹ * l = l * l₂⁻¹
    have h1 : l * l₂⁻¹ = l₂ * ((l₂⁻¹ * l) * l₂⁻¹) := by group
    rw [h1, ← hnc l₂⁻¹]
    group
  have hpow : (l₂⁻¹ * l) ^ 12 = 1 := by
    rw [hcomm.mul_pow, inv_pow, h₂ l₂ hl₂, h₁ l hl]
    simp
  have hord : orderOf (l₂⁻¹ * l) ∣ 6 * 2 := orderOf_dvd_of_pow_eq_one hpow
  have hone : orderOf (l₂⁻¹ * l) = 1 := by
    have hc6 := hcop _ hn
    have h2 : orderOf (l₂⁻¹ * l) ∣ 2 := (Nat.Coprime.dvd_mul_left hc6).mp hord
    have hc2 : Nat.Coprime (orderOf (l₂⁻¹ * l)) 2 :=
      Nat.Coprime.coprime_dvd_right (by norm_num) hc6
    exact Nat.Coprime.eq_one_of_dvd hc2 h2
  have hn1 : l₂⁻¹ * l = 1 := orderOf_eq_one_iff.mp hone
  have : l = l₂ := by
    have := congrArg (l₂ * ·) hn1
    simpa using this
  rw [this]
  exact hl₂

end CFSG.ClassicalInvolution.Q3.Q3W
