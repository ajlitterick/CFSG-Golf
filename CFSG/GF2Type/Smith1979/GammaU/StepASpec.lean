module

public import CFSG.GF2Type.Smith1979.GammaU.StepAInputs

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

theorem vecOf_two_pow (j : Fin 12) : vecOf (2 ^ (j : ℕ)) = Pi.single j 1 := by
  funext k
  simp only [vecOf, Nat.testBit_two_pow, Pi.single_apply, eq_comm (a := k), Fin.ext_iff]
  by_cases h : (j : ℕ) = k <;> simp [h]

theorem two_pow_lt (j : Fin 12) : 2 ^ (j : ℕ) < 4096 :=
  lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) j.isLt) (by norm_num)

theorem linMap_ext {f g : V12 →ₗ[ZMod 2] V12}
    (h : ∀ j : Fin 12, f (vecOf (2 ^ (j : ℕ))) = g (vecOf (2 ^ (j : ℕ)))) : f = g := by
  refine LinearMap.pi_ext fun j c => ?_
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc c with rfl | rfl
  · simp
  · rw [← vecOf_two_pow]
    exact h j

theorem appN_lt {r : Array ℕ} (hr : ∀ x ∈ r, x < 4096) (n : ℕ) : appN r n < 4096 := by
  unfold appN
  generalize (List.range 12) = l
  suffices h : ∀ acc, acc < 4096 →
      l.foldl (fun acc j => if n.testBit j then acc ^^^ r[j]! else acc) acc < 4096 from
    h 0 (by norm_num)
  induction l with
  | nil => exact fun acc h => h
  | cons j l ih =>
    intro acc hacc
    rw [List.foldl_cons]
    refine ih _ ?_
    split_ifs
    · refine xor_lt hacc ?_
      rw [getElem!_def]
      split
      · rename_i x hx
        exact hr x (Array.mem_of_getElem? hx)
      · norm_num
    · exact hacc

theorem isoN_spec {r : Array ℕ} (h : isoN r = true) :
    (∀ x ∈ r, x < 4096) ∧ ∀ x, q0 (linOfRows r x) = q0 x := by
  simp only [isoN, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨-, hlt⟩, hq⟩ := h
  refine ⟨fun x hx => ?_, forall_of_forall_code fun n hn => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
    exact hlt i hi
  · rw [← vecOf_appN, q0_vecOf, q0_vecOf, hq n hn]

theorem theta0N_lt {n : ℕ} (hn : n < 4096) : theta0N n < 4096 := by
  have h12 : (4096 : ℕ) = 2 ^ 12 := by norm_num
  rw [h12]
  refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
  have h1 : n.testBit (6 + i) = false := testBit_of_lt hn (by omega)
  have h2 : n.testBit (6 + (i - 6)) = false := testBit_of_lt hn (by omega)
  have h3 : (63 : ℕ).testBit (i - 6) = false := by
    rw [show (63 : ℕ) = 2 ^ 6 - 1 by norm_num, Nat.testBit_two_pow_sub_one,
      decide_eq_false_iff_not]
    omega
  simp only [theta0N, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    Nat.testBit_xor, Nat.testBit_and, h1, h2, h3, Bool.and_false, Bool.false_xor, Bool.false_or,
    Bool.and_false]

theorem unitary_spec {r : Array ℕ} (hr : ∀ x ∈ r, x < 4096) (h : unitaryN r = true) :
    ∀ x, linOfRows r (theta0 x) = theta0 (linOfRows r x) := by
  have hfun : (linOfRows r).comp theta0 = theta0.comp (linOfRows r) := by
    refine linMap_ext fun j => ?_
    simp only [unitaryN, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have hj := h j j.isLt
    simp only [LinearMap.comp_apply]
    rw [← vecOf_theta0N (two_pow_lt j), ← vecOf_appN, hj, vecOf_theta0N (appN_lt hr _),
      vecOf_appN]
  exact fun x => LinearMap.congr_fun hfun x

theorem anti_spec {r : Array ℕ} (hr : ∀ x ∈ r, x < 4096) (h : antiN r = true) :
    ∀ x, linOfRows r (theta0 x) = theta0 (theta0 (linOfRows r x)) := by
  have hfun : (linOfRows r).comp theta0 = theta0.comp (theta0.comp (linOfRows r)) := by
    refine linMap_ext fun j => ?_
    simp only [antiN, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have hj := h j j.isLt
    simp only [LinearMap.comp_apply]
    rw [← vecOf_theta0N (two_pow_lt j), ← vecOf_appN, hj,
      vecOf_theta0N (theta0N_lt (appN_lt hr _)), vecOf_theta0N (appN_lt hr _), vecOf_appN]
  exact fun x => LinearMap.congr_fun hfun x

@[expose] noncomputable def toU (r : Array ℕ) (h : gammaUN r = true) : V12 ≃ₗ[ZMod 2] V12 :=
  equivOfPreserves (linOfRows r)
    (isoN_spec (by simp only [gammaUN, Bool.and_eq_true] at h; exact h.1)).2

@[simp] theorem toU_apply (r : Array ℕ) (h : gammaUN r = true) (x : V12) :
    toU r h x = linOfRows r x := rfl

theorem gammaUN_spec {r : Array ℕ} (h : gammaUN r = true) : toU r h ∈ gammaU := by
  have h' := h
  simp only [gammaUN, Bool.and_eq_true, Bool.or_eq_true] at h'
  obtain ⟨hiso, hu | ha⟩ := h'
  · exact ⟨(isoN_spec hiso).2, Or.inl (unitary_spec (isoN_spec hiso).1 hu)⟩
  · exact ⟨(isoN_spec hiso).2, Or.inr (anti_spec (isoN_spec hiso).1 ha)⟩


theorem gensOK_spec (h : gensOK () = true) :
    (∀ r ∈ gamuGens, gammaUN r = true) ∧ ∀ r ∈ saGens, gammaUN r = true ∧ appN r a0 = a0 := by
  simp only [gensOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2⟩


theorem codeOf_eq_zero {x : V12} (h : codeOf x = 0) : x = 0 := by
  rw [← vecOf_codeOf x, h, vecOf_zero]

theorem q0b_codeOf (x : V12) : q0b (codeOf x) = false ↔ q0 x = 0 := by
  rw [← vecOf_codeOf x, q0_vecOf, codeOf_vecOf (codeOf_lt x)]
  cases q0b (codeOf x) <;> decide


theorem spanOf_map_appN (r : Array ℕ) (s : List ℕ) :
    spanOf (s.map (appN r)) = (spanOf s).map (linOfRows r) := by
  unfold spanOf
  rw [Submodule.map_span]
  congr 1
  ext x
  simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨vecOf v, ⟨v, hv, rfl⟩, (vecOf_appN r v).symm⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨appN r v, ⟨v, hv, rfl⟩, vecOf_appN r v⟩


end CFSG.GF2Type.Smith1979.GammaU.StepA
