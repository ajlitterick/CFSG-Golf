module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.NormCoordinates
public import CFSG.LinearAlgebra.ScalarGraphAction
public import TauCeti.GroupTheory.OrderOfElement.Basic

public section

open Polynomial

namespace CFSG.RankTwoShapes

section Linearized

variable {L : Type*} [Field L]

theorem linearized_coeff_eq_zero [Finite L] {p : ℕ} (hp : p.Prime) {m : ℕ}
    (hL : Nat.card L = p ^ m) (c : Fin m → L) (h : ∀ z : L, ∑ i, c i * z ^ p ^ (i : ℕ) = 0) :
    c = 0 := by
  classical
  have := Fintype.ofFinite L
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Subsingleton.elim _ _
  have hinj : ∀ i j : Fin m, p ^ (i : ℕ) = p ^ (j : ℕ) ↔ i = j := fun i j =>
    ⟨fun h => Fin.ext (Nat.pow_right_injective hp.two_le h), fun h => by rw [h]⟩
  let P : L[X] := ∑ i, C (c i) * X ^ p ^ (i : ℕ)
  have hP : P = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P Finset.univ
    · intro z _
      simp [P, eval_finsetSum, h z]
    · rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hL]
      calc P.natDegree ≤ p ^ (m - 1) := by
            apply natDegree_sum_le_of_forall_le
            intro i _
            exact (natDegree_C_mul_X_pow_le _ _).trans
              (Nat.pow_le_pow_right hp.pos (by omega))
        _ < p ^ m := Nat.pow_lt_pow_right hp.one_lt (by omega)
  funext j
  have hc := congrArg (fun P => Polynomial.coeff P (p ^ (j : ℕ))) hP
  simp only [P, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
  simp only [hinj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hc
  simpa using hc

def frobeniusMulAddHom {p : ℕ} [Fact p.Prime] [CharP L p] (c : L) (i : ℕ) : L →+ L where
  toFun z := c * z ^ p ^ i
  map_zero' := by simp [Fact.out (p := p.Prime) |>.pos.ne']
  map_add' x y := by rw [add_pow_char_pow, mul_add]

theorem exists_linearized_eq [Finite L] {p : ℕ} [hp : Fact p.Prime] [CharP L p] {m : ℕ}
    (hL : Nat.card L = p ^ m) (f : L →+ L) :
    ∃ c : Fin m → L, ∀ z, f z = ∑ i, c i * z ^ p ^ (i : ℕ) := by
  classical
  have := Fintype.ofFinite L
  have : Finite (L →+ L) := Finite.of_injective _ DFunLike.coe_injective
  let Φ : (Fin m → L) → (L →+ L) := fun c => ∑ i, frobeniusMulAddHom (p := p) (c i) i
  have hΦ : ∀ c z, Φ c z = ∑ i, c i * z ^ p ^ (i : ℕ) := fun c z => by
    simp [Φ, frobeniusMulAddHom]
  have hinj : Function.Injective Φ := by
    intro c d hcd
    have h0 := linearized_coeff_eq_zero hp.out hL (c - d) fun z => by
      have := congrArg (fun φ : L →+ L => φ z) hcd
      simp only [hΦ] at this
      simp [sub_mul, Finset.sum_sub_distrib, this]
    exact sub_eq_zero.mp h0
  have hcard : Nat.card (L →+ L) ≤ Nat.card (Fin m → L) := by
    let _ : Module (ZMod p) L := (ZMod.algebra L p).toModule
    have hfr : Module.finrank (ZMod p) L = m := by
      have h := Module.card_eq_pow_finrank (K := ZMod p) (V := L)
      rw [ZMod.card, ← Nat.card_eq_fintype_card, hL] at h
      exact (Nat.pow_right_injective hp.out.two_le h).symm
    let b := Module.finBasisOfFinrankEq (ZMod p) L hfr
    refine Nat.card_le_card_of_injective (fun f : L →+ L => fun i => f (b i)) ?_
    intro f g hfg
    have : f.toZModLinearMap p = g.toZModLinearMap p := b.ext fun i => congrFun hfg i
    ext z
    exact LinearMap.congr_fun this z
  obtain ⟨c, hc⟩ := (hinj.bijective_of_nat_card_le hcard).2 f
  exact ⟨c, fun z => by rw [← hc, hΦ]⟩

end Linearized


section NormRigidity

variable {L : Type} [Field L]

theorem pow_four_eq_self_of_mem_subfield {K : Subfield L} (hK : Nat.card K = 4) {t : L}
    (ht : t ∈ K) : t ^ 4 = t := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card (⟨t, ht⟩ : K)
  rw [← Nat.card_eq_fintype_card, hK] at h
  exact congrArg Subtype.val h

theorem mem_subfield_of_pow_four_eq_self (hL : Nat.card L = 16) {K : Subfield L}
    (hK : Nat.card K = 4) {t : L} (ht : t ^ 4 = t) : t ∈ K := by
  have := finite_of_natCard_eq_sixteen hL
  have hsub : (K : Set L) ⊆ {t | t ^ 4 = t} := fun t ht =>
    pow_four_eq_self_of_mem_subfield hK ht
  have heq : (K : Set L) = {t | t ^ 4 = t} := by
    apply Set.eq_of_subset_of_ncard_le hsub _ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    change Nat.card {t : L // t ^ 4 = t} ≤ Nat.card K
    rw [natCard_pow_four_eq_self hL, hK]
  have : t ∈ (K : Set L) := by rw [heq]; exact ht
  exact this

theorem add_pow_four_of_charTwo [CharP L 2] (a b : L) : (a + b) ^ 4 = a ^ 4 + b ^ 4 := by
  have := add_pow_char_pow (R := L) a b 2 2
  norm_num at this
  exact this

theorem fieldSixteen_coeffs_eq_zero_of_forall_eval (hL : Nat.card L = 16)
    (a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₂ : L)
    (h : ∀ z : L, a₁ * z + a₂ * z ^ 2 + a₃ * z ^ 3 + a₄ * z ^ 4 + a₅ * z ^ 5 + a₆ * z ^ 6 +
      a₈ * z ^ 8 + a₉ * z ^ 9 + a₁₀ * z ^ 10 + a₁₂ * z ^ 12 = 0) :
    a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 ∧ a₅ = 0 ∧ a₆ = 0 ∧ a₈ = 0 ∧ a₉ = 0 ∧ a₁₀ = 0 ∧
      a₁₂ = 0 := by
  classical
  have := finite_of_natCard_eq_sixteen hL
  let : Fintype L := Fintype.ofFinite L
  let P : L[X] := C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 + C a₄ * X ^ 4 + C a₅ * X ^ 5 +
    C a₆ * X ^ 6 + C a₈ * X ^ 8 + C a₉ * X ^ 9 + C a₁₀ * X ^ 10 + C a₁₂ * X ^ 12
  have hP : P = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P Finset.univ
    · intro z _
      simpa [P] using h z
    · rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hL]
      have : P.natDegree ≤ 12 := by
        simp only [P]
        compute_degree
      omega
  have hc : ∀ n, P.coeff n = 0 := fun n => by rw [hP, coeff_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [P, coeff_X, coeff_X_pow] using hc 1
  · simpa [P, coeff_X, coeff_X_pow] using hc 2
  · simpa [P, coeff_X, coeff_X_pow] using hc 3
  · simpa [P, coeff_X, coeff_X_pow] using hc 4
  · simpa [P, coeff_X, coeff_X_pow] using hc 5
  · simpa [P, coeff_X, coeff_X_pow] using hc 6
  · simpa [P, coeff_X, coeff_X_pow] using hc 8
  · simpa [P, coeff_X, coeff_X_pow] using hc 9
  · simpa [P, coeff_X, coeff_X_pow] using hc 10
  · simpa [P, coeff_X, coeff_X_pow] using hc 12

theorem exists_mul_pow_of_norm_comp_eq (hL : Nat.card L = 16) (K : Subfield L)
    (hK : Nat.card K = 4) (f : L →+ L) (g : K →+ K) (hf : f ≠ 0)
    (hfg : ∀ (z : L) (w : K), (w : L) = z * z ^ 4 → (g w : L) = f z * f z ^ 4) :
    ∃ (c : L) (i : Fin 4), c ≠ 0 ∧ (∀ z, f z = c * z ^ 2 ^ (i : ℕ)) ∧
      ∀ w : K, (g w : L) = c * c ^ 4 * (w : L) ^ 2 ^ (i : ℕ) := by
  have := finite_of_natCard_eq_sixteen hL
  have := charP_two_of_natCard_eq_sixteen hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨l, hl⟩ := exists_linearized_eq (p := 2) (m := 4) (by rw [hL]; norm_num) f
  obtain ⟨μ, hμ⟩ := exists_linearized_eq (L := K) (p := 2) (m := 2) (by rw [hK]; norm_num) g
  simp only [Fin.sum_univ_four] at hl
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hμ
  norm_num at hl
  have key : ∀ z : L, l 3 * l 1 ^ 4 * z + l 0 * l 2 ^ 4 * z ^ 2 +
      (l 0 * l 3 ^ 4 + l 1 * l 2 ^ 4) * z ^ 3 + l 1 * l 3 ^ 4 * z ^ 4 +
      (l 0 ^ 5 + l 2 ^ 5 - (μ 0 : L)) * z ^ 5 + (l 1 * l 0 ^ 4 + l 2 * l 3 ^ 4) * z ^ 6 +
      l 2 * l 0 ^ 4 * z ^ 8 + (l 0 * l 1 ^ 4 + l 3 * l 2 ^ 4) * z ^ 9 +
      (l 1 ^ 5 + l 3 ^ 5 - (μ 1 : L)) * z ^ 10 + (l 2 * l 1 ^ 4 + l 3 * l 0 ^ 4) * z ^ 12 = 0 := by
    intro z
    have h16 := pow_sixteen_eq_self hL z
    have hw : z * z ^ 4 ∈ K := mem_subfield_of_pow_four_eq_self hL hK (by
      have := pow_five_pow_four hL z
      rw [← pow_succ'] ; exact this)
    have hid := hfg z ⟨z * z ^ 4, hw⟩ rfl
    have hgw := congrArg Subtype.val (hμ ⟨z * z ^ 4, hw⟩)
    simp only [Subfield.coe_add, Subfield.coe_mul, SubmonoidClass.coe_pow] at hgw
    rw [hgw, hl z] at hid
    have hfrob : (l 0 * z + l 1 * z ^ 2 + l 2 * z ^ 4 + l 3 * z ^ 8) ^ 4 =
        l 2 ^ 4 * z + l 3 ^ 4 * z ^ 2 + l 0 ^ 4 * z ^ 4 + l 1 ^ 4 * z ^ 8 := by
      rw [add_pow_four_of_charTwo, add_pow_four_of_charTwo, add_pow_four_of_charTwo]
      have h32 : z ^ 32 = z ^ 2 := by
        rw [show (32 : ℕ) = 16 * 2 by norm_num, pow_mul, h16]
      ring_nf
      rw [h16, h32]
      ring
    rw [hfrob] at hid
    linear_combination -hid - (l 3 * l 1 ^ 4) * h16
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₈, e₉, e₁₀, e₁₂⟩ :=
    fieldSixteen_coeffs_eq_zero_of_forall_eval hL _ _ _ _ _ _ _ _ _ _ key
  have hμ' : ∀ w : K, (g w : L) = (μ 0 : L) * w + (μ 1 : L) * (w : L) ^ 2 := fun w => by
    have := congrArg Subtype.val (hμ w)
    simpa only [Subfield.coe_add, Subfield.coe_mul, SubmonoidClass.coe_pow] using this
  have hμ0 : (μ 0 : L) = l 0 ^ 5 + l 2 ^ 5 := (sub_eq_zero.mp e₅).symm
  have hμ1 : (μ 1 : L) = l 1 ^ 5 + l 3 ^ 5 := (sub_eq_zero.mp e₁₀).symm
  have hw4 : ∀ w : K, (w : L) ^ 4 = w := fun w => pow_four_eq_self_of_mem_subfield hK w.2
  have hpow : ∀ {a : L} {n : ℕ}, a ^ (n + 1) = 0 → a = 0 := fun h =>
    (pow_eq_zero_iff (Nat.succ_ne_zero _)).mp h
  by_cases h0 : l 0 = 0
  · by_cases h1 : l 1 = 0
    · by_cases h2 : l 2 = 0
      ·
        have h3 : l 3 ≠ 0 := by
          intro h3
          apply hf
          ext z
          rw [hl z, h0, h1, h2, h3]
          simp
        refine ⟨l 3, 3, h3, fun z => ?_, fun w => ?_⟩
        · show f z = l 3 * z ^ 8
          rw [hl z, h0, h1, h2]; ring
        · show (g w : L) = l 3 * l 3 ^ 4 * (w : L) ^ 8
          rw [hμ' w, hμ0, hμ1, h0, h1, h2]
          have : (w : L) ^ 8 = (w : L) ^ 2 := by
            rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, hw4]
          rw [this]; ring
      ·
        have h3 : l 3 = 0 := by
          rw [h0, h1] at e₉
          have : l 3 * l 2 ^ 4 = 0 := by simpa using e₉
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exact absurd (hpow h) h2
        refine ⟨l 2, 2, h2, fun z => ?_, fun w => ?_⟩
        · show f z = l 2 * z ^ 4
          rw [hl z, h0, h1, h3]; ring
        · show (g w : L) = l 2 * l 2 ^ 4 * (w : L) ^ 4
          rw [hμ' w, hμ0, hμ1, h0, h1, h3, hw4]; ring
    ·
      have h3 : l 3 = 0 := by
        rcases mul_eq_zero.mp e₄ with h | h
        · exact absurd h h1
        · exact hpow h
      have h2 : l 2 = 0 := by
        rw [h0, h3] at e₃
        have : l 1 * l 2 ^ 4 = 0 := by simpa using e₃
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h h1
        · exact hpow h
      refine ⟨l 1, 1, h1, fun z => ?_, fun w => ?_⟩
      · show f z = l 1 * z ^ 2
        rw [hl z, h0, h2, h3]; ring
      · show (g w : L) = l 1 * l 1 ^ 4 * (w : L) ^ 2
        rw [hμ' w, hμ0, hμ1, h0, h2, h3]; ring
  ·
    have h2 : l 2 = 0 := by
      rcases mul_eq_zero.mp e₂ with h | h
      · exact absurd h h0
      · exact hpow h
    have h3 : l 3 = 0 := by
      rw [h2] at e₃
      have : l 0 * l 3 ^ 4 = 0 := by simpa using e₃
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h0
      · exact hpow h
    have h1 : l 1 = 0 := by
      rw [h3] at e₉
      have : l 0 * l 1 ^ 4 = 0 := by simpa using e₉
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h0
      · exact hpow h
    refine ⟨l 0, 0, h0, fun z => ?_, fun w => ?_⟩
    · show f z = l 0 * z ^ 1
      rw [hl z, h1, h2, h3]; ring
    · show (g w : L) = l 0 * l 0 ^ 4 * (w : L) ^ 1
      rw [hμ' w, hμ0, hμ1, h1, h2, h3]; ring

theorem eq_and_eq_of_mul_pow_two_pow_eq (hL : Nat.card L = 16) {c c' : L} {i i' : Fin 4}
    (hc : c ≠ 0) (h : ∀ z : L, c * z ^ 2 ^ (i : ℕ) = c' * z ^ 2 ^ (i' : ℕ)) :
    c = c' ∧ i = i' := by
  classical
  have := finite_of_natCard_eq_sixteen hL
  have h0 := linearized_coeff_eq_zero Nat.prime_two (m := 4) (by rw [hL]; norm_num)
    (Pi.single i c - Pi.single i' c' : Fin 4 → L) fun z => by
      simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply, h z]
  have hii := congrFun (sub_eq_zero.mp h0) i
  by_cases hi : i = i'
  · subst hi
    simp only [Pi.single_eq_same] at hii
    exact ⟨hii, rfl⟩
  · simp only [Pi.single_eq_same, Pi.single_apply, hi, ite_false] at hii
    exact absurd hii hc

theorem pow_two_pow_injective_of_charTwo [CharP L 2] (i : ℕ) :
    Function.Injective (fun x : L => x ^ 2 ^ i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x y h
  exact (iterateFrobenius L 2 i).injective (by simpa [iterateFrobenius_def] using h)

theorem exists_addEquiv_norm_comp_eq (hL : Nat.card L = 16) (K : Subfield L)
    (hK : Nat.card K = 4) (c : Lˣ) (i : Fin 4) :
    ∃ (f : L ≃+ L) (g : K ≃+ K), (∀ z, f z = c * z ^ 2 ^ (i : ℕ)) ∧
      (∀ w : K, (g w : L) = c * c ^ 4 * (w : L) ^ 2 ^ (i : ℕ)) ∧
      ∀ (z : L) (w : K), (w : L) = z * z ^ 4 → (g w : L) = f z * f z ^ 4 := by
  have := finite_of_natCard_eq_sixteen hL
  have := charP_two_of_natCard_eq_sixteen hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hc0 : (c : L) ≠ 0 := c.ne_zero
  have hc5 : (c : L) * (c : L) ^ 4 ∈ K := mem_subfield_of_pow_four_eq_self hL hK (by
    rw [← pow_succ']
    exact pow_five_pow_four hL _)
  let f₀ : L →+ L := frobeniusMulAddHom (p := 2) (c : L) i
  have hf₀ : ∀ z, f₀ z = c * z ^ 2 ^ (i : ℕ) := fun z => rfl
  let g₀ : K →+ K :=
    { toFun := fun w => ⟨c * c ^ 4 * (w : L) ^ 2 ^ (i : ℕ), K.mul_mem hc5 (K.pow_mem w.2 _)⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun v w => by
        apply Subtype.ext
        simp only [Subfield.coe_add, add_pow_char_pow, mul_add] }
  have hg₀ : ∀ w : K, (g₀ w : L) = c * c ^ 4 * (w : L) ^ 2 ^ (i : ℕ) := fun w => rfl
  have hf₀inj : Function.Injective f₀ := fun x y h => by
    rw [hf₀, hf₀] at h
    exact pow_two_pow_injective_of_charTwo _ (mul_left_cancel₀ hc0 h)
  have hg₀inj : Function.Injective g₀ := fun v w h => by
    have h' := congrArg Subtype.val h
    rw [hg₀, hg₀] at h'
    exact Subtype.ext (pow_two_pow_injective_of_charTwo _ (mul_left_cancel₀ (by
      exact mul_ne_zero hc0 (pow_ne_zero _ hc0)) h'))
  refine ⟨AddEquiv.ofBijective f₀ (Finite.injective_iff_bijective.mp hf₀inj),
    AddEquiv.ofBijective g₀ (Finite.injective_iff_bijective.mp hg₀inj), hf₀, hg₀, ?_⟩
  intro z w hw
  change (g₀ w : L) = f₀ z * f₀ z ^ 4
  rw [hg₀, hf₀, hw]
  ring

theorem binaryQuadraticNorm_similarity_rigidity (hL : Nat.card L = 16) (K : Subfield L)
    (hK : Nat.card K = 4) :
    (∀ (f : L →+ L) (g : K →+ K), f ≠ 0 →
      (∀ (z : L) (w : K), (w : L) = z * z ^ 4 → (g w : L) = f z * f z ^ 4) →
      ∃! li : Lˣ × Fin 4, (∀ z, f z = li.1 * z ^ 2 ^ (li.2 : ℕ)) ∧
        ∀ w : K, (g w : L) = li.1 * li.1 ^ 4 * (w : L) ^ 2 ^ (li.2 : ℕ)) ∧
    ∀ (l : Lˣ) (i : Fin 4), ∃ (f : L ≃+ L) (g : K ≃+ K), (∀ z, f z = l * z ^ 2 ^ (i : ℕ)) ∧
      (∀ w : K, (g w : L) = l * l ^ 4 * (w : L) ^ 2 ^ (i : ℕ)) ∧
      ∀ (z : L) (w : K), (w : L) = z * z ^ 4 → (g w : L) = f z * f z ^ 4 := by
  refine ⟨fun f g hf hfg => ?_, exists_addEquiv_norm_comp_eq hL K hK⟩
  obtain ⟨c, i, hc, hfc, hgc⟩ := exists_mul_pow_of_norm_comp_eq hL K hK f g hf hfg
  refine ⟨(Units.mk0 c hc, i), ⟨hfc, hgc⟩, ?_⟩
  rintro ⟨l, j⟩ ⟨hfl, -⟩
  have hfl' : ∀ z, f z = l * z ^ 2 ^ (j : ℕ) := hfl
  obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_pow_two_pow_eq hL hc (c' := l) (i' := j) fun z => by
    rw [← hfc z, hfl' z]
  exact Prod.ext (Units.ext h1.symm) h2.symm

end NormRigidity

section GeneratedSubfield

variable {F : Type} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]


end GeneratedSubfield

section FieldSixteenDegree

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]
variable {K : IntermediateField (ZMod 2) F}


end FieldSixteenDegree

section CoordinateTransport

variable {K F V : Type*} [Semiring K]
variable [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]


end CoordinateTransport

section FieldSixteen

variable {K : Type} [Field K]

@[expose] def fieldSixteenSubfield (hK : Nat.card K = 16) : Subfield K where
  carrier := {t | t ^ 4 = t}
  mul_mem' {a b} ha hb := by
    change (a * b) ^ 4 = a * b
    change a ^ 4 = a at ha
    change b ^ 4 = b at hb
    rw [mul_pow, ha, hb]
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    have := charP_two_of_natCard_eq_sixteen hK
    change (a + b) ^ 4 = a + b
    change a ^ 4 = a at ha
    change b ^ 4 = b at hb
    rw [add_pow_four_of_charTwo, ha, hb]
  zero_mem' := by simp
  neg_mem' {a} ha := by
    change (-a) ^ 4 = -a
    change a ^ 4 = a at ha
    have := charP_two_of_natCard_eq_sixteen hK
    rw [CharTwo.neg_eq]
    exact ha
  inv_mem' a ha := by
    change a⁻¹ ^ 4 = a⁻¹
    change a ^ 4 = a at ha
    rw [inv_pow, ha]

theorem mem_fieldSixteenSubfield {hK : Nat.card K = 16} {t : K} :
    t ∈ fieldSixteenSubfield hK ↔ t ^ 4 = t :=
  Iff.rfl


end FieldSixteen


section ScalarNormalizer


end ScalarNormalizer

end CFSG.RankTwoShapes
