
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4RadCentBase

@[expose] public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Sporadic.J4
open scoped commutatorElement

@[expose] def cm {Y : Type*} [Group Y] (a : Y) : Y →* Y := (MulAut.conj a).toMonoidHom

theorem cm_apply {Y : Type*} [Group Y] (a y : Y) : cm a y = a * y * a⁻¹ := rfl

theorem cm_injective {Y : Type*} [Group Y] (a : Y) : Function.Injective (cm a) :=
  (MulAut.conj a).injective

theorem cm_comp {Y : Type*} [Group Y] (a b : Y) : (cm a).comp (cm b) = cm (a * b) := by
  ext y
  simp [cm_apply, mul_assoc]

theorem cm_comp_inv {Y : Type*} [Group Y] (a : Y) : (cm a⁻¹).comp (cm a) = MonoidHom.id Y := by
  ext y
  simp [cm_apply, mul_assoc]

theorem centralizer_image_cm {Y : Type*} [Group Y] (a : Y) (S : Set Y) :
    Subgroup.centralizer (cm a '' S) = (Subgroup.centralizer S).map (cm a) := by
  ext c
  rw [Subgroup.mem_map]
  constructor
  · intro hc
    refine ⟨a⁻¹ * c * a, ?_, by simp [cm_apply, mul_assoc]⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have := Subgroup.mem_centralizer_iff.1 hc (a * s * a⁻¹) ⟨s, hs, rfl⟩
    calc s * (a⁻¹ * c * a) = a⁻¹ * ((a * s * a⁻¹) * c) * a := by group
      _ = a⁻¹ * (c * (a * s * a⁻¹)) * a := by rw [this]
      _ = (a⁻¹ * c * a) * s := by group
  · rintro ⟨c', hc', rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hc' s hs
    show a * s * a⁻¹ * (a * c' * a⁻¹) = a * c' * a⁻¹ * (a * s * a⁻¹)
    calc a * s * a⁻¹ * (a * c' * a⁻¹) = a * (s * c') * a⁻¹ := by group
      _ = a * (c' * s) * a⁻¹ := by rw [this]
      _ = a * c' * a⁻¹ * (a * s * a⁻¹) := by group

@[expose] def radOf {Y : Type*} [Group Y] (V : Subgroup Y) : Subgroup Y :=
  pCoreOf 2 (Subgroup.normalizer (V : Set Y))

theorem radOf_map_cm {Y : Type*} [Group Y] (m : Y) (V : Subgroup Y) :
    radOf (V.map (cm m)) = (radOf V).map (cm m) := by
  unfold radOf
  rw [show V.map (cm m) = V.map (MulAut.conj m).toMonoidHom from rfl,
    normalizer_map_equiv_eq (MulAut.conj m) V,
    CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj m)]
  rfl

@[expose] def RadV {Y : Type*} [Group Y] (x₀ : Y) (V : Subgroup Y) : Prop :=
  Subgroup.centralizer (radOf V : Set Y) ≤ radOf V ∧
    16 < (radOf V ⊓ Subgroup.centralizer ({x₀} : Set Y)).relIndex (radOf V)

theorem radV_of_centralizer {Y : Type*} [Group Y] [Finite Y] {V : Subgroup Y} (x₀ : Y)
    (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hU : IsPGroup 2 (Subgroup.centralizer (V : Set Y)))
    (hidx : 16 < (Subgroup.centralizer (V : Set Y) ⊓
      Subgroup.centralizer ({x₀} : Set Y)).relIndex (Subgroup.centralizer (V : Set Y))) :
    RadV x₀ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVU : V ≤ Subgroup.centralizer (V : Set Y) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => hab b hb a ha
  have hUR : Subgroup.centralizer (V : Set Y) ≤ radOf V :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (centralizer_le_normalizer_set _)
      (normalizer_le_normalizer_centralizer _) hU
  have hVR : V ≤ radOf V := hVU.trans hUR
  exact ⟨fun c hc => hUR (Subgroup.centralizer_le (fun x hx => hVR hx) hc),
    lt_of_lt_of_le hidx (relIndex_inf_mono hUR x₀)⟩


theorem exists_conj_five {Y : Type} [Group Y] [Finite Y] (hY : ¬ 5 ^ 2 ∣ Nat.card Y) {x₀ n : Y}
    (h5 : orderOf x₀ = 5) (hn : n * x₀ * n⁻¹ = x₀ ^ 2) {x : Y} (hx : orderOf x = 5) :
    ∃ g : Y, g * x * g⁻¹ = x₀ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : ¬ 5 ^ 2 ∣ Nat.card (⊤ : Subgroup Y) := by rwa [Subgroup.card_top]
  obtain ⟨m, -, k, hk⟩ := Kc3J4.exists_conj_of_orderOf_prime (p := 5) hP (Subgroup.mem_top x₀)
    (Subgroup.mem_top x) h5 hx
  have key : ∀ j : ℕ, n ^ j * x₀ * (n ^ j)⁻¹ = x₀ ^ (2 ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc n ^ (j + 1) * x₀ * (n ^ (j + 1))⁻¹ = n * (n ^ j * x₀ * (n ^ j)⁻¹) * n⁻¹ := by
            rw [pow_succ']; group
        _ = n * x₀ ^ (2 ^ j) * n⁻¹ := by rw [ih]
        _ = (n * x₀ * n⁻¹) ^ (2 ^ j) := by rw [conj_pow]
        _ = x₀ ^ (2 ^ (j + 1)) := by rw [hn, ← pow_mul, pow_succ]; ring_nf
  have hmod : x₀ ^ k = x₀ ^ ((k % (orderOf x₀ : ℤ)).toNat) := by
    rw [← zpow_mod_orderOf, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      rw [h5]; norm_num))]
  obtain ⟨r, hr, hkr⟩ : ∃ r : ℕ, r < 5 ∧ x₀ ^ k = x₀ ^ r :=
    ⟨(k % (orderOf x₀ : ℤ)).toNat, by
      have h1 : k % (orderOf x₀ : ℤ) < 5 := by rw [h5]; exact Int.emod_lt_of_pos _ (by norm_num)
      omega, hmod⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [hkr, pow_zero, mul_one, mul_inv_cancel] at hk
    rw [hk, orderOf_one] at hx
    omega
  have hpow : ∀ j : ℕ, x₀ ^ (2 ^ j) = x₀ ^ (2 ^ j % 5) := fun j => by
    rw [← pow_mod_orderOf, h5]
  have hcase : ∃ j : ℕ, x₀ ^ r = n ^ j * x₀ * (n ^ j)⁻¹ := by
    interval_cases r
    · exact absurd rfl hr0
    · exact ⟨0, by simp⟩
    · exact ⟨1, by rw [key, pow_one]⟩
    · refine ⟨3, ?_⟩
      rw [key, hpow]
      norm_num
    · refine ⟨2, ?_⟩
      rw [key, hpow]
      norm_num
  obtain ⟨j, hj⟩ := hcase
  refine ⟨(m * n ^ j)⁻¹, ?_⟩
  rw [hk, hkr, hj]
  group


end CFSG.QuasithinUnique.A5
