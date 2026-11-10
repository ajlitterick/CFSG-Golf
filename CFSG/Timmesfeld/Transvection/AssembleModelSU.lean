module

public import CFSG.Timmesfeld.Transvection.AssembleGen
public import CFSG.Timmesfeld.Transvection.ModelRankSU
public import CFSG.Timmesfeld.Transvection.PresSUModel
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.Timmesfeld.Transvection.Pres

namespace ModelRank

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

@[expose] def PerpUU (j : ℕ) (v : Fin m → F) : Prop :=
  ∀ i : Fin (m / 2), i.val < j → v (lowIdx i) = 0 ∧ v (Fin.rev (lowIdx i)) = 0

theorem PerpUU.add {j : ℕ} {v w : Fin m → F} (hv : PerpUU j v) (hw : PerpUU j w) :
    PerpUU j (v + w) := fun i hi => by
  simp [(hv i hi).1, (hv i hi).2, (hw i hi).1, (hw i hi).2]

theorem PerpUU.sub {j : ℕ} {v w : Fin m → F} (hv : PerpUU j v) (hw : PerpUU j w) :
    PerpUU j (v - w) := fun i hi => by
  simp [(hv i hi).1, (hv i hi).2, (hw i hi).1, (hw i hi).2]

theorem PerpUU.smul {j : ℕ} {v : Fin m → F} (hv : PerpUU j v) (l : F) : PerpUU j (l • v) :=
  fun i hi => by simp [(hv i hi).1, (hv i hi).2]

theorem PerpUU.uForm_eq_zero {j : ℕ} {v : Fin m → F} (hv : PerpUU j v) {i : Fin (m / 2)}
    (hi : i.val < j) : uForm σ v (Pi.single (lowIdx i) 1) = 0 ∧
      uForm σ v (Pi.single (Fin.rev (lowIdx i)) 1) = 0 := by
  rw [uForm_single_right, uForm_single_right, Fin.rev_rev, (hv i hi).1, (hv i hi).2, map_zero]
  exact ⟨rfl, rfl⟩

theorem PerpUU.exists_uForm_ne_zero {j : ℕ} {w : Fin m → F} (hw : PerpUU j w) (hw0 : w ≠ 0) :
    ∃ a, PerpUU j a ∧ uForm σ w a ≠ 0 := by
  obtain ⟨s, hs⟩ := Function.ne_iff.1 hw0
  refine ⟨Pi.single (Fin.rev s) 1, fun i hi => ⟨?_, ?_⟩, ?_⟩
  · have : lowIdx i ≠ Fin.rev s := fun h => hs (by
      rw [← Fin.rev_rev s, ← h]
      exact (hw i hi).2)
    simp [this]
  · have : Fin.rev (lowIdx i) ≠ Fin.rev s := fun h => hs (by
      rw [← Fin.rev_injective h]
      exact (hw i hi).1)
    simp [this]
  · rw [uForm_single_right, Fin.rev_rev, map_ne_zero]
    exact hs

variable (hσ : ∀ c, σ (σ c) = c)
include hσ

theorem PerpUU.exists_isotropic (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {j : ℕ}
    {w w' : Fin m → F} (hw : PerpUU j w) (hw' : PerpUU j w') (hw0 : w ≠ 0) (hw'0 : w' ≠ 0)
    (hww : uForm σ w w = 0) (hww' : uForm σ w w' = 0) :
    ∃ z, PerpUU j z ∧ uForm σ z z = 0 ∧ uForm σ w z ≠ 0 ∧ uForm σ w' z ≠ 0 := by
  obtain ⟨a, ha, hwa⟩ := hw.exists_uForm_ne_zero hw0
  obtain ⟨b, hb, hw'b⟩ := hw'.exists_uForm_ne_zero hw'0
  obtain ⟨y, hy, hwy, hw'y⟩ : ∃ y, PerpUU j y ∧ uForm σ w y ≠ 0 ∧ uForm σ w' y ≠ 0 := by
    by_cases h1 : uForm σ w' a = 0
    · by_cases h2 : uForm σ w b = 0
      · refine ⟨a + b, ha.add hb, ?_, ?_⟩
        · rw [uForm_add_right, h2, add_zero]
          exact hwa
        · rw [uForm_add_right, h1, zero_add]
          exact hw'b
      · exact ⟨b, hb, h2, hw'b⟩
    · exact ⟨a, ha, hwa, h1⟩
  obtain ⟨s, hs⟩ := htr (-uForm σ y y) (by rw [map_neg, uForm_conj σ hσ])
  have hσd : σ (uForm σ w y) ≠ 0 := (map_ne_zero σ).2 hwy
  have hw'w : uForm σ w' w = 0 := uForm_eq_zero_comm hσ hww'
  have hyw : uForm σ y w = σ (uForm σ w y) := (uForm_conj σ hσ w y).symm
  refine ⟨y + (s / σ (uForm σ w y)) • w, hy.add (hw.smul _), ?_, ?_, ?_⟩
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hww, hyw]
    have e1 : s / σ (uForm σ w y) * σ (uForm σ w y) = s := div_mul_cancel₀ s hσd
    have e2 : σ (s / σ (uForm σ w y)) * uForm σ w y = σ s := by
      rw [map_div₀, hσ, div_mul_cancel₀ _ hwy]
    linear_combination e1 + e2 + hs
  · rw [uForm_add_right, uForm_smul_right, hww, mul_zero, add_zero]
    exact hwy
  · rw [uForm_add_right, uForm_smul_right, hw'w, mul_zero, add_zero]
    exact hw'y

theorem exists_suMat_mulVec_eq_fix {x y : Fin m → F} (hxx : uForm σ x x = 0)
    (hyy : uForm σ y y = 0) (hxy : uForm σ x y ≠ 0) (hxy' : uForm σ x y + σ (uForm σ x y) = 0) :
    ∃ g : SU σ m, suMat σ m g *ᵥ x = y ∧ ∀ z, uForm σ (y - x) z = 0 → suMat σ m g *ᵥ z = z := by
  have hyx : uForm σ y x = σ (uForm σ x y) := (uForm_conj σ hσ x y).symm
  have hσd : σ (uForm σ x y) = -uForm σ x y := by linear_combination hxy'
  have hσd0 : σ (uForm σ x y) ≠ 0 := (map_ne_zero σ).2 hxy
  have hu : uForm σ (y - x) (y - x) = 0 := by
    rw [uForm_sub_left, uForm_sub_right, uForm_sub_right, hxx, hyy, hyx]
    linear_combination -hxy'
  have hc : (σ (uForm σ x y))⁻¹ + σ (σ (uForm σ x y))⁻¹ = 0 := by
    rw [map_inv₀, hσ, hσd, inv_neg, neg_add_cancel]
  obtain ⟨g, hg⟩ := exists_suMat_eq_uTrans hσ hu hc
  refine ⟨g, ?_, fun z hz => ?_⟩
  · rw [hg, uTrans_mulVec, uForm_sub_left, hxx, sub_zero, hyx, inv_mul_cancel₀ hσd0, one_smul,
      add_sub_cancel]
  · rw [hg, uTrans_mulVec, hz, mul_zero, zero_smul, add_zero]

theorem exists_suMat_mulVec_eq_smul_of_perp (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {ζ : F}
    (hζ : ζ ≠ 0) (hζ' : ζ + σ ζ = 0) {j : ℕ} {w w' : Fin m → F} (hw : PerpUU j w)
    (hw' : PerpUU j w') (hw0 : w ≠ 0) (hw'0 : w' ≠ 0) (hww : uForm σ w w = 0)
    (hw'w' : uForm σ w' w' = 0) :
    ∃ (g : SU σ m) (l : F), l ≠ 0 ∧ suMat σ m g *ᵥ w = l • w' ∧ ∀ i : Fin (m / 2), i.val < j →
      suMat σ m g *ᵥ Pi.single (lowIdx i) 1 = Pi.single (lowIdx i) 1 ∧
      suMat σ m g *ᵥ Pi.single (Fin.rev (lowIdx i)) 1 = Pi.single (Fin.rev (lowIdx i)) 1 := by
  have step : ∀ {x y : Fin m → F}, PerpUU j x → PerpUU j y → uForm σ x x = 0 →
      uForm σ y y = 0 → uForm σ x y ≠ 0 → ∃ g : SU σ m,
        suMat σ m g *ᵥ x = (ζ / uForm σ x y) • y ∧ ∀ i : Fin (m / 2), i.val < j →
          suMat σ m g *ᵥ Pi.single (lowIdx i) 1 = Pi.single (lowIdx i) 1 ∧
          suMat σ m g *ᵥ Pi.single (Fin.rev (lowIdx i)) 1 = Pi.single (Fin.rev (lowIdx i)) 1 := by
    intro x y hx hy hxx hyy hxy
    have hxy1 : uForm σ x ((ζ / uForm σ x y) • y) = ζ := by
      rw [uForm_smul_right, div_mul_cancel₀ _ hxy]
    have hyy1 : uForm σ ((ζ / uForm σ x y) • y) ((ζ / uForm σ x y) • y) = 0 := by
      rw [uForm_smul_left, uForm_smul_right, hyy, mul_zero, mul_zero]
    obtain ⟨g, hg, hfix⟩ := exists_suMat_mulVec_eq_fix hσ hxx hyy1 (by rw [hxy1]; exact hζ)
      (by rw [hxy1]; exact hζ')
    have hu : PerpUU j ((ζ / uForm σ x y) • y - x) := (hy.smul _).sub hx
    exact ⟨g, hg, fun i hi => ⟨hfix _ (hu.uForm_eq_zero hi).1, hfix _ (hu.uForm_eq_zero hi).2⟩⟩
  by_cases hww' : uForm σ w w' = 0
  · obtain ⟨z, hz, hzz, hwz, hw'z⟩ := hw.exists_isotropic hσ htr hw' hw0 hw'0 hww hww'
    obtain ⟨g₁, hg₁, hfix₁⟩ := step hw hz hww hzz hwz
    set z₁ := (ζ / uForm σ w z) • z with hz₁
    have hz₁U : PerpUU j z₁ := hz.smul _
    have hz₁z₁ : uForm σ z₁ z₁ = 0 := by
      rw [hz₁, uForm_smul_left, uForm_smul_right, hzz, mul_zero, mul_zero]
    have hz₁w' : uForm σ z₁ w' ≠ 0 := by
      rw [hz₁, uForm_smul_left, ← uForm_conj σ hσ w' z]
      exact mul_ne_zero ((map_ne_zero σ).2 (div_ne_zero hζ hwz)) ((map_ne_zero σ).2 hw'z)
    obtain ⟨g₂, hg₂, hfix₂⟩ := step hz₁U hw' hz₁z₁ hw'w' hz₁w'
    refine ⟨g₂ * g₁, ζ / uForm σ z₁ w', div_ne_zero hζ hz₁w', ?_, fun i hi => ⟨?_, ?_⟩⟩
    · rw [map_mul, ← mulVec_mulVec, hg₁, hg₂]
    · rw [map_mul, ← mulVec_mulVec, (hfix₁ i hi).1, (hfix₂ i hi).1]
    · rw [map_mul, ← mulVec_mulVec, (hfix₁ i hi).2, (hfix₂ i hi).2]
  · obtain ⟨g, hg, hfix⟩ := step hw hw' hww hw'w' hww'
    exact ⟨g, ζ / uForm σ w w', div_ne_zero hζ hww', hg, hfix⟩


end ModelRank

open ModelRank


section Line

include hj


end Line

end CFSG.Timmesfeld.Transvection
