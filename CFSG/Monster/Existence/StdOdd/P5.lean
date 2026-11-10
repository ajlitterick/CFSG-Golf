module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Rank
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.SemidirectProduct
public import Std.Data.HashSet
public import Std.Data.HashMap
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public meta import Std.Data.HashSet
public meta import Std.Data.HashMap
public import Certificates.Certificate6040
public import CFSG.Certificates.Kernel.WeylE6Sound

public section

namespace CFSG.Monster.Existence.StdOdd

namespace P5

abbrev GL5 : Type := Matrix.GeneralLinearGroup (Fin 5) (ZMod 3)

theorem refl_mul_self (i : Fin 6) : refl i * refl i = 1 := by
  fin_cases i <;> decide +kernel

@[expose] def reflGL (i : Fin 6) : GL5 := ⟨refl i, refl i, refl_mul_self i, refl_mul_self i⟩

@[expose] def Wgrp : Subgroup GL5 := Subgroup.closure (Set.range reflGL)

@[expose] def genA : GL5 := reflGL 1 * reflGL 3

@[expose] def genB : GL5 :=
  reflGL 2 * reflGL 3 * reflGL 4 * reflGL 5 * reflGL 0 * reflGL 2 * reflGL 3 * reflGL 4

@[expose] def Pbar : Subgroup GL5 := Subgroup.closure {genA, genB}


theorem genA_val : (genA : M5) = aMat := by decide +kernel
theorem genB_val : (genB : M5) = bMat := by decide +kernel

@[expose] def letter : Fin 2 → GL5 := ![genA, genB]

@[expose] def letterM : Fin 2 → M5 := ![aMat, bMat]

@[expose] def wordProd (w : List (Fin 2)) : GL5 := (w.map letter).prod

theorem pmat_ra : ∀ i : Fin 81, pmat (ra i) = pmat i * aMat :=
  Certificates.certificate6040.1
theorem pmat_rb : ∀ i : Fin 81, pmat (rb i) = pmat i * bMat :=
  Certificates.certificate6040.2.1
theorem pmat_inj : ∀ i j : Fin 81, pmat i = pmat j → i = j :=
  Certificates.certificate6040.2.2.1
theorem pmat_zero : pmat 0 = 1 :=
  Certificates.certificate6040.2.2.2.1
theorem walk_pw : ∀ j : Fin 81, walk (pw j) 0 = j :=
  Certificates.certificate6040.2.2.2.2.1
theorem tb_eq : ∀ i j : Fin 81, tb i j = walk (pw j) i :=
  Certificates.certificate6040.2.2.2.2.2.1
theorem tb_inv : ∀ i : Fin 81, ∃ j : Fin 81, tb i j = 0 :=
  Certificates.certificate6040.2.2.2.2.2.2.1

theorem pmat_walk (w : List (Fin 2)) (i : Fin 81) :
    pmat (walk w i) = pmat i * (w.map letterM).prod := by
  induction w generalizing i with
  | nil => simp [walk]
  | cons c w ih =>
    rw [walk, ih, List.map_cons, List.prod_cons, ← mul_assoc]
    congr 1
    fin_cases c
    · simp [step, pmat_ra, letterM]
    · simp [step, pmat_rb, letterM]

theorem pmat_eq_word
    (j : Fin 81) : pmat j = ((pw j).map letterM).prod := by
  have := pmat_walk (pw j) 0
  rwa [walk_pw, pmat_zero, one_mul] at this

theorem wordProd_val (w : List (Fin 2)) : ((wordProd w : GL5) : M5) = (w.map letterM).prod := by
  induction w with
  | nil => simp [wordProd]
  | cons c w ih =>
    have h : ((wordProd (c :: w) : GL5) : M5) = (letter c : M5) * (wordProd w : M5) := by
      simp [wordProd]
    rw [h, ih, List.map_cons, List.prod_cons]
    congr 1
    fin_cases c <;> simp [letter, letterM, genA_val, genB_val]

@[expose] def pm (j : Fin 81) : GL5 := wordProd (pw j)

theorem pm_val (j : Fin 81) : ((pm j : GL5) : M5) = pmat j := by
  rw [pm, wordProd_val, ← pmat_eq_word]

theorem pm_ra (i : Fin 81) : pm (ra i) = pm i * genA :=
  Units.ext (by simp [pm_val, pmat_ra, genA_val])

theorem pm_rb (i : Fin 81) : pm (rb i) = pm i * genB :=
  Units.ext (by simp [pm_val, pmat_rb, genB_val])

theorem pm_zero : pm 0 = 1 := Units.ext (by simp [pm_val, pmat_zero])

theorem pm_step
    (c : Fin 2) (i : Fin 81) : pm (step c i) = pm i * letter c := by
  fin_cases c
  · simp [step, pm_ra, letter]
  · simp [step, pm_rb, letter]

theorem pm_walk
    (w : List (Fin 2)) (i : Fin 81) : pm (walk w i) = pm i * wordProd w := by
  induction w generalizing i with
  | nil => simp [walk, wordProd]
  | cons c w ih =>
    rw [walk, ih, pm_step, mul_assoc]
    simp [wordProd]

theorem pm_tb (i j : Fin 81) : pm (tb i j) = pm i * pm j := by
  rw [tb_eq, pm_walk]; rfl

theorem pm_injective : Function.Injective pm :=
  fun i j h => pmat_inj i j (by rw [← pm_val, ← pm_val, h])

theorem letter_mem (c : Fin 2) : letter c ∈ Pbar := by
  fin_cases c
  · exact Subgroup.subset_closure (by simp [letter])
  · exact Subgroup.subset_closure (by simp [letter])

theorem pm_mem_Pbar (j : Fin 81) : pm j ∈ Pbar := by
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
  exact letter_mem c

@[expose] def PS : Subgroup GL5 where
  carrier := Set.range pm
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨tb i j, pm_tb i j⟩
  one_mem' := ⟨0, pm_zero⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := tb_inv i
    refine ⟨j, ?_⟩
    have : pm i * pm j = 1 := by rw [← pm_tb, hj, pm_zero]
    exact (eq_inv_of_mul_eq_one_right this)

theorem Pbar_eq_PS : Pbar = PS := by
  apply le_antisymm
  · rw [Pbar, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨ra 0, by rw [pm_ra, pm_zero, one_mul]⟩
    · exact ⟨rb 0, by rw [pm_rb, pm_zero, one_mul]⟩
  · rintro _ ⟨i, rfl⟩
    exact pm_mem_Pbar i

theorem mem_Pbar_iff (g : GL5) : g ∈ Pbar ↔ ∃ i, pm i = g := by
  rw [Pbar_eq_PS]; rfl

theorem card_Pbar : Nat.card Pbar = 81 := by
  rw [Pbar_eq_PS]
  exact (Nat.card_range_of_injective pm_injective).trans (by simp)

def IsClosedSet (T : Finset (Fin 81)) : Prop :=
  T.card = 81 ∨ ∀ u ∈ T, ∀ v ∈ T, tb u v ∈ T

theorem closedL_iff (T : Finset (Fin 81)) : closedL (sortFin T) = true ↔ IsClosedSet T := by
  simp [closedL, IsClosedSet, sortFin, List.all_eq_true]

theorem latticeClosedB_true : latticeClosedB = true :=
  Certificates.certificate6040.2.2.2.2.2.2.2.1

theorem lattice_zero : [0] ∈ lattice :=
  Certificates.certificate6040.2.2.2.2.2.2.2.2.1


theorem lattice_closed
    (l : List (Fin 81)) (hl : l ∈ lattice) (x : Fin 81) (hx : x ∉ l.toFinset)
    (hc : IsClosedSet (extSet l.toFinset x)) : sortFin (extSet l.toFinset x) ∈ lattice := by
  have h := latticeClosedB_true
  simp only [latticeClosedB, List.all_eq_true] at h
  have h2 := h l hl x (List.mem_finRange x)
  have hx' : x ∉ l := by simpa using hx
  have hc' := (closedL_iff _).mpr hc
  simpa [checkLat, hx', hc'] using h2

open Classical in
noncomputable def idx (H : Subgroup GL5) : Finset (Fin 81) := Finset.univ.filter fun i => pm i ∈ H

theorem mem_idx {H : Subgroup GL5} {i : Fin 81} : i ∈ idx H ↔ pm i ∈ H := by
  simp [idx]

theorem exists_coset_rep {G : Type*} [Group G] (H H' : Subgroup G) (hle : H' ≤ H) {m : ℕ}
    (hH : Nat.card H = 3 ^ (m + 1)) (hH' : Nat.card H' = 3 ^ m) :
    ∃ x ∈ H, x ∉ H' ∧ ∀ h ∈ H, ∃ k < 3, (x ^ k)⁻¹ * h ∈ H' := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; positivity)
  set K : Subgroup H := H'.subgroupOf H with hK
  have hKcard : Nat.card K = 3 ^ m := by
    rw [← hH']; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hidx : K.index = 3 := by
    have h1 := K.card_mul_index
    rw [hKcard, hH, pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hKn : K.Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hidx, hH, Nat.Prime.pow_minFac Nat.prime_three (by omega)]
  have hQcard : Nat.card (H ⧸ K) = 3 := by rw [← Subgroup.index_eq_card]; exact hidx
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : H, x₀ ∉ K := by
    by_contra hcon
    have hK1 : K = ⊤ := (Subgroup.eq_top_iff' K).mpr fun x => not_not.mp (not_exists.mp hcon x)
    rw [hK1, Subgroup.card_top, hH] at hKcard
    have h3 : 3 ^ m * 3 = 3 ^ m * 1 := by rw [← pow_succ, hKcard, mul_one]
    exact absurd (Nat.eq_of_mul_eq_mul_left (by positivity) h3) (by norm_num)
  have hne : ((x₀ : H ⧸ K)) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  have hord : orderOf (x₀ : H ⧸ K) = 3 := by
    apply orderOf_eq_prime _ hne
    rw [← hQcard]
    exact pow_card_eq_one'
  have htop : Subgroup.zpowers (x₀ : H ⧸ K) = ⊤ := zpowers_eq_top_of_prime_card hQcard hne
  refine ⟨x₀.1, x₀.2, ?_, ?_⟩
  · intro hx
    exact hx₀ (by simpa [hK, Subgroup.mem_subgroupOf] using hx)
  · intro h hh
    have hmem : (((⟨h, hh⟩ : H) : H ⧸ K)) ∈ Subgroup.zpowers (x₀ : H ⧸ K) := by
      rw [htop]; trivial
    rw [mem_zpowers_iff_mem_range_orderOf, hord] at hmem
    obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hmem
    refine ⟨k, Finset.mem_range.mp hk, ?_⟩
    have h2 : (x₀ ^ k)⁻¹ * ⟨h, hh⟩ ∈ K := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_pow]; exact hkx
    simpa [hK, Subgroup.mem_subgroupOf] using h2

theorem idx_ext
    {H H' : Subgroup GL5} (hH : H ≤ Pbar) (hle : H' ≤ H) {x₀ : Fin 81}
    (hx : pm x₀ ∈ H) (hcos : ∀ h ∈ H, ∃ k < 3, (pm x₀ ^ k)⁻¹ * h ∈ H') :
    idx H = extSet (idx H') x₀ := by
  ext i
  simp only [extSet, Finset.mem_union, Finset.mem_image, mem_idx]
  constructor
  · intro hi
    obtain ⟨k, hk, hn⟩ := hcos _ hi
    obtain ⟨j, hj⟩ := (mem_Pbar_iff _).mp (hH (hle hn))
    have hjH' : pm j ∈ H' := by rw [hj]; exact hn
    have hpi : pm i = pm x₀ ^ k * pm j := by rw [hj]; group
    interval_cases k
    · left; left
      rw [show pm i = pm j by simpa using hpi]; exact hjH'
    · left; right
      refine ⟨j, hjH', pm_injective ?_⟩
      rw [pm_tb, hpi]; simp
    · right
      refine ⟨j, hjH', pm_injective ?_⟩
      rw [pm_tb, pm_tb, hpi, pow_two, mul_assoc]
  · rintro ((h1 | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩)
    · exact hle h1
    · rw [pm_tb]; exact H.mul_mem hx (hle ha)
    · rw [pm_tb, pm_tb]; exact H.mul_mem hx (H.mul_mem hx (hle ha))

theorem idx_mem_lattice_aux :
    ∀ (m : ℕ) (H : Subgroup GL5), H ≤ Pbar → Nat.card H = 3 ^ m →
      ∃ l ∈ lattice, l.toFinset = idx H := by
  intro m
  induction m with
  | zero =>
    intro H hH hcard
    have hbot : H = ⊥ := Subgroup.eq_bot_of_card_eq H (by simpa using hcard)
    have : idx H = {0} := by
      ext i
      rw [mem_idx, hbot, Finset.mem_singleton, Subgroup.mem_bot, ← pm_zero]
      exact ⟨fun h => pm_injective h, fun h => by rw [h]⟩
    exact ⟨[0], lattice_zero, by rw [this]; rfl⟩
  | succ m ih =>
    intro H hH hcard
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := m)
      (by rw [hcard]; exact pow_dvd_pow 3 (Nat.le_succ m))
    set H' : Subgroup GL5 := K.map H.subtype with hH'
    have hH'card : Nat.card H' = 3 ^ m := by
      rw [hH', Subgroup.card_map_of_injective H.subtype_injective, hK]
    have hle : H' ≤ H := Subgroup.map_subtype_le K
    obtain ⟨l', hl', hl'H⟩ := ih H' (hle.trans hH) hH'card
    obtain ⟨x, hxH, hxH', hcos⟩ := exists_coset_rep H H' hle hcard hH'card
    obtain ⟨x₀, rfl⟩ := (mem_Pbar_iff x).mp (hH hxH)
    have hext := idx_ext hH hle hxH hcos
    have hclosed : IsClosedSet (extSet l'.toFinset x₀) := by
      rw [hl'H]
      rw [← hext]
      right
      intro u hu v hv
      rw [mem_idx] at hu hv ⊢
      rw [pm_tb]
      exact H.mul_mem hu hv
    have hnot : x₀ ∉ l'.toFinset := by rw [hl'H, mem_idx]; exact hxH'
    refine ⟨_, lattice_closed l' hl' x₀ hnot hclosed, ?_⟩
    rw [sortFin, Finset.sort_toFinset, hl'H, hext]

theorem idx_mem_lattice (H : Subgroup GL5) (hH : H ≤ Pbar) :
    ∃ l ∈ lattice, l.toFinset = idx H := by
  have hd : Nat.card H ∣ 3 ^ 4 := by
    have := Subgroup.card_dvd_of_le hH
    rw [card_Pbar] at this
    simpa using this
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  exact idx_mem_lattice_aux m H hH hm

@[expose] def fixedVecs (A : Set GL5) : Set E5 := {v | ∀ g ∈ A, (g : M5).mulVec v = v}

theorem elemCheckB_true : elemCheckB = true :=
  Certificates.certificate6040.2.2.2.2.2.2.2.2.2.2.1

theorem latticeNodup : ∀ l ∈ lattice, l.Nodup :=
  Certificates.certificate6040.2.2.2.2.2.2.2.2.2.2.2.1

theorem card_eq_idx_card
    (H : Subgroup GL5) (hH : H ≤ Pbar) : Nat.card H = (idx H).card := by
  have hset : (H : Set GL5) = pm '' (idx H : Set (Fin 81)) := by
    ext g
    constructor
    · intro hg
      obtain ⟨i, rfl⟩ := (mem_Pbar_iff g).mp (hH hg)
      exact ⟨i, by simpa [mem_idx] using hg, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      simpa [mem_idx] using hi
  calc Nat.card H = Nat.card (H : Set GL5) := rfl
    _ = Nat.card (pm '' (idx H : Set (Fin 81))) := by rw [hset]
    _ = Nat.card (idx H : Set (Fin 81)) := Nat.card_image_of_injective pm_injective _
    _ = (idx H).card := by simp

theorem fixedVecs_card
    (H : Subgroup GL5) (hH : H ≤ Pbar) (l : List (Fin 81))
    (hl : l.toFinset = idx H) : Nat.card (fixedVecs (H : Set GL5)) = fixedCardL l := by
  classical
  have hmem : ∀ i, i ∈ l ↔ pm i ∈ H := fun i => by rw [← mem_idx, ← hl]; simp
  have hset : fixedVecs (H : Set GL5) = {v | ∀ i ∈ l, (pmat i).mulVec v = v} := by
    ext v
    simp only [fixedVecs, Set.mem_ofPred_eq, SetLike.mem_coe]
    constructor
    · intro h i hi
      simpa [pm_val] using h _ ((hmem i).mp hi)
    · intro h g hg
      obtain ⟨i, rfl⟩ := (mem_Pbar_iff g).mp (hH hg)
      simpa [pm_val] using h i ((hmem i).mpr hg)
  rw [hset, fixedCardL, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Set.mem_ofPred_eq]

theorem elemAbelian_bound
    (A : Subgroup GL5) (hA : A ≤ Pbar) (h3 : ∀ g ∈ A, g ^ 3 = 1)
    (hc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g) (hne : A ≠ ⊥) :
    Nat.card A * Nat.card (fixedVecs (A : Set GL5)) ≤ 81 := by
  obtain ⟨l, hl, hlA⟩ := idx_mem_lattice A hA
  have hmem : ∀ i, i ∈ l ↔ pm i ∈ A := fun i => by rw [← mem_idx, ← hlA]; simp
  have hcard : Nat.card A = l.length := by
    rw [card_eq_idx_card A hA, ← hlA, List.toFinset_card_of_nodup (latticeNodup l hl)]
  rw [hcard, fixedVecs_card A hA l hlA]
  have h := elemCheckB_true
  simp only [elemCheckB, List.all_eq_true] at h
  have h1 := h l hl
  have hel : elemAbL l = true := by
    simp only [elemAbL, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    intro i hi
    refine ⟨pm_injective ?_, fun j hj => pm_injective ?_⟩
    · rw [pm_tb, pm_tb, pm_zero]
      have := h3 _ ((hmem i).mp hi)
      rwa [pow_three'] at this
    · rw [pm_tb, pm_tb]; exact hc _ ((hmem i).mp hi) _ ((hmem j).mp hj)
  have hn0 : l ≠ [0] := by
    rintro rfl
    apply hne
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨i, rfl⟩ := (mem_Pbar_iff g).mp (hA hg)
    have : i ∈ [(0 : Fin 81)] := (hmem i).mpr hg
    rw [List.mem_singleton.mp this, pm_zero]
    exact Subgroup.one_mem _
  simpa [hel, hn0] using h1


section Extension

variable {T : Type*} [Group T]

@[expose] def ivec (E : Subgroup T) (ι : E ≃* Multiplicative E5) (e : E) : E5 :=
  Multiplicative.toAdd (ι e)

structure IsExt (P : Subgroup GL5) (E : Subgroup T) (ι : E ≃* Multiplicative E5)
    (ρ : T →* GL5) : Prop where
  normal : E.Normal
  conj : ∀ (t : T) (e : E),
    ivec E ι ⟨t * e * t⁻¹, normal.conj_mem _ e.2 t⟩ = (ρ t : M5).mulVec (ivec E ι e)
  ker : ρ.ker = E
  range : ρ.range = P

theorem card_of_equiv {E : Subgroup T} (ι : E ≃* Multiplicative E5) : Nat.card E = 3 ^ 5 := by
  rw [Nat.card_congr ι.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

namespace IsExt

variable {P : Subgroup GL5} {E : Subgroup T} {ι : E ≃* Multiplicative E5} {ρ : T →* GL5}

theorem ivec_mul (a b : E) : ivec E ι (a * b) = ivec E ι a + ivec E ι b := by
  simp [ivec]

theorem ivec_one : ivec E ι 1 = 0 := by simp [ivec]

theorem ivec_inv (a : E) : ivec E ι a⁻¹ = - ivec E ι a := by simp [ivec]

theorem ivec_injective : Function.Injective (ivec E ι) := fun _ _ h =>
  ι.injective (Multiplicative.toAdd.injective h)

theorem exists_ivec (v : E5) : ∃ e : E, ivec E ι e = v :=
  ⟨ι.symm (Multiplicative.ofAdd v), by simp [ivec]⟩

theorem card_T (h : IsExt P E ι ρ) : Nat.card T = 3 ^ 5 * Nat.card P := by
  have := Subgroup.card_ker_mul_card_range ρ
  rw [h.ker, h.range, card_of_equiv ι] at this
  exact this.symm

theorem eq_pow_five_of_dvd {d : ℕ} (h : d ∣ 3 ^ 5) (hlt : 3 ^ 4 < d) : d = 3 ^ 5 := by
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h
  interval_cases k <;> simp_all

theorem elemAbelian_le (h : IsExt P E ι ρ)
    (hP : ∀ A : Subgroup GL5, A ≤ P → (∀ g ∈ A, g ^ 3 = 1) →
      (∀ g ∈ A, ∀ k ∈ A, g * k = k * g) → A ≠ ⊥ →
      Nat.card A * Nat.card (fixedVecs (A : Set GL5)) ≤ 3 ^ 4)
    (A : Subgroup T) (hA3 : ∀ a ∈ A, a ^ 3 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A ≤ 3 ^ 5 ∧ (3 ^ 4 < Nat.card A → A = E) := by
  have hEc : Nat.card E = 3 ^ 5 := card_of_equiv ι
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; positivity)
  have hmul : Nat.card (A.map ρ) * Nat.card (ρ.ker ⊓ A : Subgroup T) = Nat.card A := by
    rw [← Subgroup.relIndex_ker, Subgroup.relIndex_mul_card]
  by_cases hbot : A.map ρ = ⊥
  · have hAE : A ≤ E := by
      rw [← h.ker]; exact (Subgroup.map_eq_bot_iff A).mp hbot
    have hdvd : Nat.card A ∣ 3 ^ 5 := hEc ▸ Subgroup.card_dvd_of_le hAE
    refine ⟨Nat.le_of_dvd (by positivity) hdvd, fun hlt => ?_⟩
    apply Subgroup.eq_of_le_of_card_ge hAE
    rw [hEc, eq_pow_five_of_dvd hdvd hlt]
  · have hAbP : A.map ρ ≤ P := by rw [← h.range]; exact Subgroup.map_le_range ρ A
    have h3 : ∀ g ∈ A.map ρ, g ^ 3 = 1 := by
      rintro _ ⟨a, ha, rfl⟩; rw [← map_pow, hA3 a ha, map_one]
    have hc : ∀ g ∈ A.map ρ, ∀ k ∈ A.map ρ, g * k = k * g := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩; rw [← map_mul, ← map_mul, hAc a ha b hb]
    have hfix := hP _ hAbP h3 hc hbot
    have hker : ∀ a : (ρ.ker ⊓ A : Subgroup T), (a : T) ∈ E := fun a => by
      rw [← h.ker]; exact a.2.1
    have hinj : Nat.card (ρ.ker ⊓ A : Subgroup T) ≤
        Nat.card (fixedVecs ((A.map ρ : Subgroup GL5) : Set GL5)) := by
      have : Finite (fixedVecs ((A.map ρ : Subgroup GL5) : Set GL5)) := inferInstance
      refine Nat.card_le_card_of_injective
        (fun a => (⟨ivec E ι ⟨a, hker a⟩, ?_⟩ : fixedVecs ((A.map ρ : Subgroup GL5) : Set GL5)))
        ?_
      · rintro _ ⟨b, hb, rfl⟩
        rw [← h.conj b ⟨a, hker a⟩]
        congr 1
        apply Subtype.ext
        show b * (a : T) * b⁻¹ = a
        rw [hAc b hb a a.2.2, mul_assoc, mul_inv_cancel, mul_one]
      · intro a a' haa
        have : ivec E ι ⟨a, hker a⟩ = ivec E ι ⟨a', hker a'⟩ := congrArg Subtype.val haa
        exact Subtype.ext (Subtype.mk.inj (ivec_injective (ι := ι) this))
    have hAle : Nat.card A ≤ 3 ^ 4 := by
      calc Nat.card A = Nat.card (A.map ρ) * Nat.card (ρ.ker ⊓ A : Subgroup T) := hmul.symm
        _ ≤ Nat.card (A.map ρ) * Nat.card (fixedVecs ((A.map ρ : Subgroup GL5) : Set GL5)) :=
          Nat.mul_le_mul_left _ hinj
        _ ≤ 3 ^ 4 := hfix
    exact ⟨hAle.trans (by norm_num), fun hlt => absurd hlt (not_lt.mpr hAle)⟩

end IsExt

end Extension

section Generation

variable {T : Type*} [Group T] {P : Subgroup GL5} {E : Subgroup T}
  {ι : E ≃* Multiplicative E5} {ρ : T →* GL5}

def Avec (E : Subgroup T) (ι : E ≃* Multiplicative E5) (F : Subgroup T) : Set E5 :=
  {v | ∃ a : E, (a : T) ∈ F ∧ ivec E ι a = v}

def AvecSub (E : Subgroup T) (ι : E ≃* Multiplicative E5) (F : Subgroup T) : AddSubgroup E5 where
  carrier := Avec E ι F
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, F.mul_mem ha hb, IsExt.ivec_mul a b⟩
  zero_mem' := ⟨1, F.one_mem, IsExt.ivec_one⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, F.inv_mem ha, IsExt.ivec_inv a⟩


theorem IsExt.closure_eq (h : IsExt P E ι ρ) (F : Subgroup T) (L J : Set T)
    (hL : L ⊆ F) (hJF : J ⊆ F) (hgen : Subgroup.closure (ρ '' L) = F.map ρ)
    (ws : Set E5)
    (hws : ∀ w ∈ ws, ∃ g ∈ F.map ρ, ∃ j ∈ J, ∃ hj : j ∈ E,
      w = (g : M5).mulVec (ivec E ι ⟨j, hj⟩))
    (hspan : ∀ a : E, (a : T) ∈ F → ivec E ι a ∈ AddSubgroup.closure ws) :
    Subgroup.closure (L ∪ J) = F := by
  set F' := Subgroup.closure (L ∪ J) with hF'
  have hF'F : F' ≤ F := by
    rw [hF', Subgroup.closure_le]
    exact Set.union_subset hL hJF
  have hLF' : ∀ f ∈ Subgroup.closure L, f ∈ F' := fun f hf =>
    Subgroup.closure_mono Set.subset_union_left hf
  have hJ' : ∀ j ∈ J, j ∈ F' := fun j hj => Subgroup.subset_closure (Or.inr hj)
  have hmapL : (Subgroup.closure L).map ρ = F.map ρ := by rw [MonoidHom.map_closure, hgen]
  apply le_antisymm hF'F
  let V : AddSubgroup E5 := AvecSub E ι F'
  have hwsV : ws ⊆ V := by
    intro w hw
    obtain ⟨g, hg, j, hj, hjE, rfl⟩ := hws w hw
    rw [← hmapL] at hg
    obtain ⟨f', hf', rfl⟩ := hg
    refine ⟨⟨f' * j * f'⁻¹, h.normal.conj_mem _ hjE f'⟩, ?_, h.conj f' ⟨j, hjE⟩⟩
    exact F'.mul_mem (F'.mul_mem (hLF' _ hf') (hJ' j hj)) (F'.inv_mem (hLF' _ hf'))
  have hA : ∀ a : E, (a : T) ∈ F → (a : T) ∈ F' := by
    intro a ha
    obtain ⟨a', ha', hv⟩ := (AddSubgroup.closure_le V).mpr hwsV (hspan a ha)
    have : a' = a := IsExt.ivec_injective hv
    exact this ▸ ha'
  intro f hf
  have h1 : ρ f ∈ (Subgroup.closure L).map ρ := by rw [hmapL]; exact ⟨f, hf, rfl⟩
  obtain ⟨f', hf'L, hf'⟩ := h1
  have hmem : f'⁻¹ * f ∈ E := by
    rw [← h.ker, MonoidHom.mem_ker, map_mul, map_inv, hf', inv_mul_cancel]
  have hF : f'⁻¹ * f ∈ F := F.mul_mem (F.inv_mem (hF'F (hLF' _ hf'L))) hf
  have hA' := hA ⟨f'⁻¹ * f, hmem⟩ hF
  have : f = f' * (f'⁻¹ * f) := by group
  rw [this]
  exact F'.mul_mem (hLF' _ hf'L) hA'

def GenData (Q : Subgroup GL5) (A : Set E5) (n : ℕ) : Prop :=
  ∃ (gens : Finset GL5) (mods : Finset E5), gens.card + mods.card ≤ n ∧ (gens : Set GL5) ⊆ Q ∧
    Subgroup.closure (gens : Set GL5) = Q ∧ (mods : Set E5) ⊆ A ∧
    A ⊆ AddSubgroup.closure {w | ∃ q ∈ Q, ∃ v ∈ mods, w = (q : M5).mulVec v}

theorem IsExt.exists_finset_of_genData (h : IsExt P E ι ρ) (F : Subgroup T) {n : ℕ}
    (hg : GenData (F.map ρ) (Avec E ι F) n) :
    ∃ S : Finset T, S.card ≤ n ∧ Subgroup.closure (S : Set T) = F := by
  classical
  obtain ⟨gens, mods, hcard, hgensQ, hgencl, hmodsA, hspan⟩ := hg
  let liftF : GL5 → T := fun g =>
    if hg : g ∈ F.map ρ then Classical.choose (Subgroup.mem_map.mp hg) else 1
  have hliftF : ∀ g ∈ F.map ρ, liftF g ∈ F ∧ ρ (liftF g) = g := fun g hg => by
    simp only [liftF, hg, ↓reduceDIte]
    exact Classical.choose_spec (Subgroup.mem_map.mp hg)
  let liftV : E5 → T := fun v => ((ι.symm (Multiplicative.ofAdd v) : E) : T)
  have hliftV : ∀ v ∈ Avec E ι F, liftV v ∈ F ∧ ∃ hj : liftV v ∈ E,
      ivec E ι ⟨liftV v, hj⟩ = v := by
    rintro v ⟨a, ha, rfl⟩
    have h1 : ι.symm (Multiplicative.ofAdd (ivec E ι a)) = a := by simp [ivec]
    have h2 : liftV (ivec E ι a) = (a : T) := by simp only [liftV, h1]
    have hjE : liftV (ivec E ι a) ∈ E := by rw [h2]; exact a.2
    exact ⟨by rw [h2]; exact ha, hjE, congrArg (ivec E ι) (Subtype.ext h2)⟩
  have hclo := h.closure_eq F (liftF '' (gens : Set GL5)) (liftV '' (mods : Set E5))
    (by rintro _ ⟨g, hg, rfl⟩; exact (hliftF g (hgensQ hg)).1)
    (by rintro _ ⟨v, hv, rfl⟩; exact (hliftV v (hmodsA hv)).1)
    (by
      have : ρ '' (liftF '' (gens : Set GL5)) = (gens : Set GL5) := by
        ext g
        constructor
        · rintro ⟨_, ⟨g', hg', rfl⟩, rfl⟩
          rw [(hliftF g' (hgensQ hg')).2]; exact hg'
        · intro hg
          exact ⟨liftF g, ⟨g, hg, rfl⟩, (hliftF g (hgensQ hg)).2⟩
      rw [this]; exact hgencl)
    {w | ∃ q ∈ F.map ρ, ∃ v ∈ mods, w = (q : M5).mulVec v}
    (by
      rintro w ⟨q, hq, v, hv, rfl⟩
      obtain ⟨hvF, hjE, hvv⟩ := hliftV v (hmodsA hv)
      exact ⟨q, hq, liftV v, ⟨v, hv, rfl⟩, hjE, by rw [hvv]⟩)
    (fun a ha => hspan ⟨a, ha, rfl⟩)
  refine ⟨gens.image liftF ∪ mods.image liftV, ?_, ?_⟩
  · calc (gens.image liftF ∪ mods.image liftV).card
        ≤ (gens.image liftF).card + (mods.image liftV).card := Finset.card_union_le _ _
      _ ≤ gens.card + mods.card := add_le_add Finset.card_image_le Finset.card_image_le
      _ ≤ n := hcard
  · rw [← hclo]
    congr 1
    simp

end Generation

section Rank

variable {T : Type*} [Group T] {P : Subgroup GL5} {E : Subgroup T}
  {ι : E ≃* Multiplicative E5} {ρ : T →* GL5}

structure PData (P : Subgroup GL5) : Prop where
  card : Nat.card P = 81
  elemAb : ∀ A : Subgroup GL5, A ≤ P → (∀ g ∈ A, g ^ 3 = 1) →
    (∀ g ∈ A, ∀ k ∈ A, g * k = k * g) → A ≠ ⊥ →
    Nat.card A * Nat.card (fixedVecs (A : Set GL5)) ≤ 3 ^ 4
  gen_top : GenData P Set.univ 3
  gen_max : ∀ Q : Subgroup GL5, Q ≤ P → Nat.card Q = 27 → GenData Q Set.univ 4
  gen_hyp : ∀ V : AddSubgroup E5, Nat.card V = 3 ^ 4 → (∀ p ∈ P, ∀ v ∈ V, (p : M5).mulVec v ∈ V) →
    (∀ p ∈ P, ∀ v : E5, (p : M5).mulVec v - v ∈ V) → GenData P (V : Set E5) 3

theorem IsExt.card_eq (h : IsExt P E ι ρ) (hd : PData P) : Nat.card T = 3 ^ 9 := by
  rw [h.card_T, hd.card]; norm_num

theorem IsExt.rank_top (h : IsExt P E ι ρ) (hd : PData P) :
    ∃ S : Finset T, S.card ≤ 3 ∧ Subgroup.closure (S : Set T) = ⊤ := by
  apply h.exists_finset_of_genData ⊤
  have h1 : (⊤ : Subgroup T).map ρ = P := by rw [← MonoidHom.range_eq_map, h.range]
  have h2 : Avec E ι ⊤ = Set.univ := by
    ext v
    simp only [Avec, Set.mem_univ, iff_true]
    obtain ⟨e, he⟩ := IsExt.exists_ivec (ι := ι) v
    exact ⟨e, Subgroup.mem_top _, he⟩
  rw [h1, h2]
  exact hd.gen_top

theorem IsExt.rank_eight (h : IsExt P E ι ρ) (hd : PData P) (F : Subgroup T)
    (hF : Nat.card F = 3 ^ 8) :
    ∃ S : Finset T, S.card ≤ 4 ∧ Subgroup.closure (S : Set T) = F := by
  have hT : Nat.card T = 3 ^ 9 := h.card_eq hd
  have hEc : Nat.card E = 3 ^ 5 := card_of_equiv ι
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; positivity)
  set Q := F.map ρ with hQ
  have hQP : Q ≤ P := by rw [← h.range]; exact Subgroup.map_le_range ρ F
  have hmul : Nat.card Q * Nat.card (E ⊓ F : Subgroup T) = 3 ^ 8 := by
    have := Subgroup.relIndex_mul_card ρ.ker F
    rw [Subgroup.relIndex_ker, h.ker] at this
    rw [← hF]; exact this
  have hQd : Nat.card Q ∣ 3 ^ 4 := by
    have := Subgroup.card_dvd_of_le hQP
    rwa [hd.card, (by norm_num : (81 : ℕ) = 3 ^ 4)] at this
  have hAd : Nat.card (E ⊓ F : Subgroup T) ∣ 3 ^ 5 := hEc ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hiQ⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hQd
  obtain ⟨j, hj, hjA⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hAd
  rw [hiQ, hjA, ← pow_add] at hmul
  have hij : i + j = 8 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hmul
  have hcases : (i = 3 ∧ j = 5) ∨ (i = 4 ∧ j = 4) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    have hEF : E ≤ F := by
      have : E ⊓ F = E := Subgroup.eq_of_le_of_card_ge (inf_le_left : E ⊓ F ≤ E)
        (by rw [hEc, hjA])
      exact inf_eq_left.mp this
    have hA : Avec E ι F = Set.univ := by
      ext v
      simp only [Avec, Set.mem_univ, iff_true]
      obtain ⟨e, he⟩ := IsExt.exists_ivec (ι := ι) v
      exact ⟨e, hEF e.2, he⟩
    apply h.exists_finset_of_genData F
    rw [hA]
    exact hd.gen_max Q hQP (by rw [hiQ]; norm_num)
  ·
    have hQeq : Q = P :=
      Subgroup.eq_of_le_of_card_ge hQP (by rw [hd.card, hiQ]; norm_num)
    have hidx : F.index = 3 := by
      have h1 := F.card_mul_index
      rw [hF, hT] at h1
      exact Nat.eq_of_mul_eq_mul_left (by positivity) (by rw [h1, pow_succ])
    have hFn : F.Normal := Subgroup.normal_of_index_eq_minFac_card
      (by rw [hidx, hT, Nat.Prime.pow_minFac Nat.prime_three (by omega)])
    have hcyc : IsCyclic (T ⧸ F) :=
      isCyclic_of_prime_card (p := 3) (by rw [← Subgroup.index_eq_card]; exact hidx)
    have hcommF : ∀ x y : T, x * y * x⁻¹ * y⁻¹ ∈ F := by
      intro x y
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [mul_assoc, (IsMulCommutative.is_comm.comm (x : T ⧸ F) (y : T ⧸ F) : _ = _)]
      simp
    set V := AvecSub E ι F with hV
    have hVcard : Nat.card V = 3 ^ 4 := by
      have : Nat.card (E ⊓ F : Subgroup T) = Nat.card V :=
        Nat.card_congr (Equiv.ofBijective
          (fun x : (E ⊓ F : Subgroup T) => (⟨ivec E ι ⟨x, x.2.1⟩, ⟨x, x.2.1⟩, x.2.2, rfl⟩ : V))
          ⟨fun x y hxy => by
            have h2 := IsExt.ivec_injective (ι := ι) (congrArg Subtype.val hxy)
            exact Subtype.ext (Subtype.mk.inj h2),
           fun ⟨v, a, ha, hv⟩ => ⟨⟨a, a.2, ha⟩, Subtype.ext hv⟩⟩)
      rw [← this, hjA]
    have hinv : ∀ p ∈ P, ∀ v ∈ V, (p : M5).mulVec v ∈ V := by
      intro p hp v hv
      rw [← hQeq] at hp
      obtain ⟨f, hf, rfl⟩ := hp
      obtain ⟨a, ha, rfl⟩ := hv
      refine ⟨⟨f * a * f⁻¹, h.normal.conj_mem _ a.2 f⟩, ?_, h.conj f a⟩
      exact F.mul_mem (F.mul_mem hf ha) (F.inv_mem hf)
    have hcomm : ∀ p ∈ P, ∀ v : E5, (p : M5).mulVec v - v ∈ V := by
      intro p hp v
      have hp' : p ∈ ρ.range := h.range ▸ hp
      obtain ⟨t, rfl⟩ := hp'
      obtain ⟨e, rfl⟩ := IsExt.exists_ivec (ι := ι) v
      refine ⟨⟨t * e * t⁻¹, h.normal.conj_mem _ e.2 t⟩ * e⁻¹, ?_, ?_⟩
      · simpa using hcommF t e
      · rw [IsExt.ivec_mul, IsExt.ivec_inv, h.conj t e, sub_eq_add_neg]
    have hg : GenData P (Avec E ι F) 3 := hd.gen_hyp V hVcard hinv hcomm
    rw [← hQeq] at hg
    obtain ⟨S, hS, hS'⟩ := h.exists_finset_of_genData F hg
    exact ⟨S, hS.trans (by norm_num), hS'⟩

end Rank

theorem card_E5 : Nat.card E5 = 3 ^ 5 := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem closure_range_card_ge {m : ℕ} (ws : Fin m → E5)
    (h : ∀ c : Fin m → ZMod 3, ∑ i, c i • ws i = 0 → c = 0) :
    3 ^ m ≤ Nat.card (AddSubgroup.closure (Set.range ws)) := by
  have hmem : ∀ c : Fin m → ZMod 3, ∑ i, c i • ws i ∈ AddSubgroup.closure (Set.range ws) := by
    intro c
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have : c i • ws i = (c i).val • ws i := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
    rw [this]
    exact AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  have hinj : Function.Injective
      (fun c : Fin m → ZMod 3 =>
        (⟨∑ i, c i • ws i, hmem c⟩ : ↥(AddSubgroup.closure (Set.range ws)))) := by
    intro c c' hcc
    have h1 : ∑ i, c i • ws i = ∑ i, c' i • ws i := congrArg Subtype.val hcc
    have h2 : ∑ i, (c - c') i • ws i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self]
    exact sub_eq_zero.mp (h _ h2)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem closure_range_eq_top {ws : Fin 5 → E5}
    (h : ∀ c : Fin 5 → ZMod 3, ∑ i, c i • ws i = 0 → c = 0) :
    AddSubgroup.closure (Set.range ws) = ⊤ := by
  apply AddSubgroup.eq_top_of_le_card
  rw [card_E5]
  exact closure_range_card_ge ws h

theorem wsT_indep :
    ∀ c : Fin 5 → ZMod 3, ∑ i, c i • wsT i = 0 → c = 0 :=
  Certificates.certificate6040.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem genA_mem : genA ∈ Pbar := Subgroup.subset_closure (by simp)
theorem genB_mem : genB ∈ Pbar := Subgroup.subset_closure (by simp)

theorem genData_top : GenData Pbar Set.univ 3 := by
  classical
  refine ⟨{genA, genB}, {eA5}, ?_, ?_, ?_, ?_, ?_⟩
  · calc ({genA, genB} : Finset GL5).card + ({eA5} : Finset E5).card
        ≤ 2 + 1 := Nat.add_le_add Finset.card_le_two (by simp)
      _ = 3 := rfl
  · intro g hg
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    exacts [genA_mem, genB_mem]
  · simp [Pbar]
  · exact Set.subset_univ _
  · intro v _
    have h1 : AddSubgroup.closure (Set.range wsT) = ⊤ := closure_range_eq_top wsT_indep
    have h2 : v ∈ AddSubgroup.closure (Set.range wsT) := by rw [h1]; trivial
    refine AddSubgroup.closure_mono ?_ h2
    rintro _ ⟨k, rfl⟩
    exact ⟨pm (selT k), pm_mem_Pbar _, eA5, by simp, by simp [wsT, pm_val]⟩

theorem e1_eq : aMat.mulVec eA5 - eA5 = e1 := by decide

theorem ws1_indep :
    ∀ c : Fin 4 → ZMod 3, ∑ i, c i • ws1 i = 0 → c = 0 :=
  Certificates.certificate6040.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem genData_hyp (V : AddSubgroup E5) (hV : Nat.card V = 3 ^ 4)
    (hinv : ∀ p ∈ Pbar, ∀ v ∈ V, (p : M5).mulVec v ∈ V)
    (hcomm : ∀ p ∈ Pbar, ∀ v : E5, (p : M5).mulVec v - v ∈ V) :
    GenData Pbar (V : Set E5) 3 := by
  classical
  have he1 : e1 ∈ V := by
    have := hcomm genA genA_mem eA5
    rwa [genA_val, e1_eq] at this
  have hws : ∀ k, ws1 k ∈ V := fun k => by
    have := hinv (pm (sel1 k)) (pm_mem_Pbar _) e1 he1
    simpa [ws1, pm_val] using this
  have hle : AddSubgroup.closure (Set.range ws1) ≤ V := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact hws k
  have hge : Nat.card V ≤ Nat.card (AddSubgroup.closure (Set.range ws1)) := by
    rw [hV]; exact closure_range_card_ge ws1 ws1_indep
  have heq : AddSubgroup.closure (Set.range ws1) = V := AddSubgroup.eq_of_le_of_card_ge hle hge
  refine ⟨{genA, genB}, {e1}, ?_, ?_, ?_, ?_, ?_⟩
  · calc ({genA, genB} : Finset GL5).card + ({e1} : Finset E5).card
        ≤ 2 + 1 := Nat.add_le_add Finset.card_le_two (by simp)
      _ = 3 := rfl
  · intro g hg
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    exacts [genA_mem, genB_mem]
  · simp [Pbar]
  · simpa using he1
  · intro v hv
    rw [← heq] at hv
    refine AddSubgroup.closure_mono ?_ hv
    rintro _ ⟨k, rfl⟩
    exact ⟨pm (sel1 k), pm_mem_Pbar _, e1, by simp, by simp [ws1, pm_val]⟩

theorem closureFin_sound
    (gens : List (Fin 81)) (i : Fin 81) (hi : i ∈ closureFin gens) :
    pm i ∈ Subgroup.closure (pm '' {g | g ∈ gens}) := by
  have key : ∀ n : ℕ, ∀ i ∈ (closureStep gens)^[n] {0},
      pm i ∈ Subgroup.closure (pm '' {g | g ∈ gens}) := by
    intro n
    induction n with
    | zero =>
      intro i hi
      rw [Function.iterate_zero_apply, Finset.mem_singleton] at hi
      rw [hi, pm_zero]
      exact Subgroup.one_mem _
    | succ n ih =>
      intro i hi
      rw [Function.iterate_succ_apply'] at hi
      simp only [closureStep, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset,
        List.mem_map] at hi
      rcases hi with hi | ⟨s, hs, g, hg, rfl⟩
      · exact ih i hi
      · rw [pm_tb]
        exact Subgroup.mul_mem _ (ih s hs) (Subgroup.subset_closure ⟨g, hg, rfl⟩)
  exact key 8 i hi

theorem cert27CheckB_true : cert27CheckB = true :=
  Certificates.certificate6040.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert27_all (l : List (Fin 81)) (hl : l ∈ lattice) :
    l.length ≠ 27 ∨ ∃ c ∈ cert27, Cert27Ok l c := by
  have h := cert27CheckB_true
  simp only [cert27CheckB, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true] at h
  exact h l hl

theorem genData_max
    (Q : Subgroup GL5) (hQ : Q ≤ Pbar) (hc : Nat.card Q = 27) :
    GenData Q Set.univ 4 := by
  classical
  obtain ⟨l, hl, hlQ⟩ := idx_mem_lattice Q hQ
  have hmem : ∀ i, i ∈ l ↔ pm i ∈ Q := fun i => by rw [← mem_idx, ← hlQ]; simp
  have hlen : l.length = 27 := by
    rw [← List.toFinset_card_of_nodup (latticeNodup l hl), hlQ, ← card_eq_idx_card Q hQ, hc]
  obtain ⟨c, hcm, hok⟩ : ∃ c ∈ cert27, Cert27Ok l c := by
    rcases cert27_all l hl with h | h
    · exact absurd hlen h
    · exact h
  obtain ⟨hcl, hcard, hgl, hsel, hindep⟩ := hok
  have hgenQ : ∀ g ∈ c.gens, pm g ∈ Q := fun g hg => (hmem g).mp (hgl g hg)
  refine ⟨(c.gens.map pm).toFinset, c.mods.toFinset, ?_, ?_, ?_, ?_, ?_⟩
  · calc (c.gens.map pm).toFinset.card + c.mods.toFinset.card
        ≤ (c.gens.map pm).length + c.mods.length :=
          Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
      _ = c.gens.length + c.mods.length := by rw [List.length_map]
      _ ≤ 4 := hcard
  · intro g hg
    simp only [List.coe_toFinset, Set.mem_ofPred_eq, List.mem_map] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    exact hgenQ i hi
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      simp only [List.coe_toFinset, Set.mem_ofPred_eq, List.mem_map] at hg
      obtain ⟨i, hi, rfl⟩ := hg
      exact hgenQ i hi
    · intro q hq
      obtain ⟨i, rfl⟩ := (mem_Pbar_iff q).mp (hQ hq)
      have hi : i ∈ closureFin c.gens := by
        rw [hcl, List.mem_toFinset, hmem]; exact hq
      have := closureFin_sound c.gens i hi
      convert this using 2
      ext g
      simp
  · exact Set.subset_univ _
  · intro v _
    have hws : ∀ k, c.vec k ∈ {w | ∃ q ∈ Q, ∃ v ∈ c.mods.toFinset, w = (q : M5).mulVec v} :=
      fun k => ⟨pm (c.sel k).1, (hmem _).mp (hsel k).1, (c.sel k).2,
        List.mem_toFinset.mpr (hsel k).2, by simp [Cert27.vec, pm_val]⟩
    have h1 : AddSubgroup.closure (Set.range c.vec) = ⊤ := closure_range_eq_top hindep
    have h2 : v ∈ AddSubgroup.closure (Set.range c.vec) := by rw [h1]; trivial
    refine AddSubgroup.closure_mono ?_ h2
    rintro _ ⟨k, rfl⟩
    exact hws k

theorem pData_Pbar : PData Pbar where
  card := card_Pbar
  elemAb := fun A hA h3 hc hne => by
    simpa using elemAbelian_bound A hA h3 hc hne
  gen_top := genData_top
  gen_max := genData_max
  gen_hyp := genData_hyp


theorem refl_apply : ∀ (i : Fin 6) (v : E5),
    (refl i).mulVec v = v - bil v (alpha i) • alpha i :=
  Certificates.certificate6040.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


theorem card_rkFibre_30 : (rkFibre 30).card = 72 :=
  Certificates.certificate6040.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem card_rkFibre_18 : (rkFibre 18).card = 80 :=
  Certificates.certificate6040.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem card_rkFibre_24 : (rkFibre 24).card = 90 :=
  Certificates.certificate6040.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


theorem decV_encV : ∀ x : E5, decV (encV x) = x :=
  Certificates.certificate6040.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


theorem fixed_card_modEq_of_stable (σ : Equiv.Perm E5) (h11 : σ ^ 11 = 1) (B : Finset E5)
    (hB : ∀ x, σ x ∈ B ↔ x ∈ B) : B.card ≡ (B.filter fun x => σ x = x).card [MOD 11] := by
  classical
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hpow : (σ.subtypePerm (p := (· ∈ B)) hB) ^ 11 = 1 := by
    ext ⟨x, hx⟩
    have h1 := Equiv.Perm.subtypePerm_pow σ 11 hB
    rw [h1]
    simp [h11]
  have hmod := Equiv.Perm.card_fixedPoints_modEq
    (f := (⇑(σ.subtypePerm (p := (· ∈ B)) hB) : Function.End {x : E5 // x ∈ B}))
    (p := 11) (n := 1) (by
      rw [pow_one]
      have h2 := Equiv.Perm.coe_pow (σ.subtypePerm (p := (· ∈ B)) hB) 11
      rw [hpow, Equiv.Perm.coe_one] at h2
      exact h2.symm)
  have hcard : Fintype.card {x : E5 // x ∈ B} = B.card := Fintype.card_coe B
  have hfix : Fintype.card (Function.fixedPoints
      (⇑(σ.subtypePerm (p := (· ∈ B)) hB) : Function.End {x : E5 // x ∈ B})) =
      (B.filter fun x => σ x = x).card := by
    rw [Fintype.card_subtype]
    apply Finset.card_bij (fun y _ => y.1)
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.mem_fixedPoints,
        Function.IsFixedPt, Equiv.Perm.subtypePerm_apply] at hy ⊢
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · intro y _ y' _ h
      exact Subtype.ext h
    · intro x hx
      simp only [Finset.mem_filter] at hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.mem_fixedPoints,
        Function.IsFixedPt, Equiv.Perm.subtypePerm_apply]
      exact Subtype.ext hx.2
  rw [hcard, hfix] at hmod
  exact hmod

theorem fixed_card_modEq (σ : Equiv.Perm E5) (h0 : σ 0 = 0) (h11 : σ ^ 11 = 1)
    (hrk : ∀ x, rk (σ x) = rk x) (c : ℕ) :
    (rkFibre c).card ≡ ((rkFibre c).filter fun x => σ x = x).card [MOD 11] := by
  refine fixed_card_modEq_of_stable σ h11 (rkFibre c) fun x => ?_
  have h1 : σ x ≠ 0 ↔ x ≠ 0 := by
    constructor
    · intro h hx; apply h; rw [hx, h0]
    · intro h hx; apply h; apply σ.injective; rw [hx, h0]
  simp only [rkFibre, Finset.mem_filter, Finset.mem_univ, true_and, hrk x, h1]

theorem fixed_card_ge_of_pow_eleven
    (σ : Equiv.Perm E5) (h0 : σ 0 = 0) (h11 : σ ^ 11 = 1)
    (hrk : ∀ x, rk (σ x) = rk x) :
    6 ≤ ((rkFibre 30).filter fun x => σ x = x).card ∧
      3 ≤ ((rkFibre 18).filter fun x => σ x = x).card ∧
      2 ≤ ((rkFibre 24).filter fun x => σ x = x).card := by
  have h30 := fixed_card_modEq σ h0 h11 hrk 30
  have h18 := fixed_card_modEq σ h0 h11 hrk 18
  have h24 := fixed_card_modEq σ h0 h11 hrk 24
  rw [card_rkFibre_30] at h30
  rw [card_rkFibre_18] at h18
  rw [card_rkFibre_24] at h24
  unfold Nat.ModEq at h30 h18 h24
  omega


section PbarExt

variable {T : Type*} [Group T] {E : Subgroup T} {ι : E ≃* Multiplicative E5} {ρ : T →* GL5}

theorem IsExt.pbar_card
    (h : IsExt Pbar E ι ρ) : Nat.card T = 3 ^ 9 := h.card_eq pData_Pbar

theorem IsExt.pbar_elemAbelian
    (h : IsExt Pbar E ι ρ) (A : Subgroup T) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A ≤ 3 ^ 5 ∧ (3 ^ 4 < Nat.card A → A = E) :=
  h.elemAbelian_le (fun A hA h3 hc hne => by simpa using elemAbelian_bound A hA h3 hc hne)
    A hA3 hAc

theorem E5_nsmul_three (v : E5) : (3 : ℕ) • v = 0 := by
  ext i
  have : ∀ z : ZMod 3, (3 : ℕ) • z = 0 := by decide
  simpa using this (v i)

theorem mul_three_E5 (x : Multiplicative E5) : x ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  exact E5_nsmul_three _

theorem IsExt.elementary_E (_h : IsExt Pbar E ι ρ) :
    Nat.card E = 3 ^ 5 ∧ (∀ a ∈ E, a ^ 3 = 1) ∧ ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
  refine ⟨card_of_equiv ι, fun a ha => ?_, fun a ha b hb => ?_⟩
  · have h1 : (⟨a, ha⟩ : E) ^ 3 = 1 :=
      ι.injective (by rw [map_pow, mul_three_E5, map_one])
    simpa using congrArg Subtype.val h1
  · have h1 : (⟨a, ha⟩ : E) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      ι.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
    simpa using congrArg Subtype.val h1


theorem IsExt.pbar_map_eq
    (h : IsExt Pbar E ι ρ) (α : T ≃* T) : E.map α.toMonoidHom = E := by
  obtain ⟨hEc, hE3, hEc'⟩ := h.elementary_E
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; positivity)
  apply (h.pbar_elemAbelian (E.map α.toMonoidHom) ?_ ?_).2
  · rw [Subgroup.card_map_of_injective α.injective, hEc]; norm_num
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, hE3 a ha, map_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hEc' a ha b hb]

theorem IsExt.pbar_rank_top (h : IsExt Pbar E ι ρ) :
    ∃ S : Finset T, S.card ≤ 3 ∧ Subgroup.closure (S : Set T) = ⊤ := h.rank_top pData_Pbar

theorem IsExt.pbar_rank_eight
    (h : IsExt Pbar E ι ρ) (F : Subgroup T) (hF : Nat.card F = 3 ^ 8) :
    ∃ S : Finset T, S.card ≤ 4 ∧ Subgroup.closure (S : Set T) = F := h.rank_eight pData_Pbar F hF

theorem IsExt.pbar_groupRank_top
    (h : IsExt Pbar E ι ρ) [Finite T] : Group.rank T ≤ 3 := by
  obtain ⟨S, hS, hcl⟩ := h.pbar_rank_top
  exact (Group.rank_le hcl).trans hS

theorem IsExt.pbar_groupRank_eight
    (h : IsExt Pbar E ι ρ) [Finite T] (F : Subgroup T)
    (hF : Nat.card F = 3 ^ 8) : Group.rank F ≤ 4 := by
  obtain ⟨S, hS, hcl⟩ := h.pbar_rank_eight F hF
  have hrk := Subgroup.rank_closure_finset_le_card S
  rw [Subgroup.rank_congr hcl] at hrk
  exact hrk.trans hS

end PbarExt

theorem card_Wgrp : Nat.card Wgrp = 51840 := by
  obtain ⟨T, P, E, s, hT, h⟩ :=
    Certificates.certificate6040.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact CFSG.KC.WeylE6.card_closure_of_wOK hT h reflGL fun _ => rfl


instance :
    Finite Wgrp := Nat.finite_of_card_ne_zero (by rw [card_Wgrp]; norm_num)


section Conj

variable {T : Type*} [Group T] {P : Subgroup GL5} {E : Subgroup T}
  {ι : E ≃* Multiplicative E5} {ρ : T →* GL5}


end Conj


section SylowExt

variable {T : Type*} [Group T] {Q : Subgroup GL5} {E : Subgroup T}
  {ι : E ≃* Multiplicative E5} {ρ : T →* GL5}


end SylowExt


section OfAction

variable {T : Type*} [Group T] {E : Subgroup T} {ι : E ≃* Multiplicative E5}

def ConjActs (hE : E.Normal) (ι : E ≃* Multiplicative E5) (t : T) (g : GL5) : Prop :=
  ∀ e : E, ivec E ι ⟨t * e * t⁻¹, hE.conj_mem _ e.2 t⟩ = (g : M5).mulVec (ivec E ι e)

theorem ConjActs.unique {hE : E.Normal} {t : T} {g g' : GL5} (h : ConjActs hE ι t g)
    (h' : ConjActs hE ι t g') : g = g' := by
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  obtain ⟨e, rfl⟩ := IsExt.exists_ivec (ι := ι) v
  rw [← h e, ← h' e]

theorem ConjActs.one (hE : E.Normal) : ConjActs hE ι (1 : T) 1 := by
  intro e
  simp

theorem ConjActs.mul {hE : E.Normal} {t t' : T} {g g' : GL5} (h : ConjActs hE ι t g)
    (h' : ConjActs hE ι t' g') : ConjActs hE ι (t * t') (g * g') := by
  intro e
  have h1 := h ⟨t' * e * t'⁻¹, hE.conj_mem _ e.2 t'⟩
  rw [h' e] at h1
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← h1]
  congr 1
  apply Subtype.ext
  show t * t' * (e : T) * (t * t')⁻¹ = t * (t' * e * t'⁻¹) * t⁻¹
  group


end OfAction

end P5

end CFSG.Monster.Existence.StdOdd
