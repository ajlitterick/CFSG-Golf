module

public import CFSG.LocalAnalysis.StandardType.GGForkAffinePairGen
public import CFSG.LocalAnalysis.StandardType.GGForkNullPos

public section

namespace CFSG.StandardType


private theorem lw_comp_symm_map {Λ Λ' : Type} (e : Λ ≃ Λ') (b : Option Λ) :
    (Equiv.optionCongr e).symm (Option.map e b) = b := by
  rw [← Equiv.optionCongr_apply]
  exact Equiv.symm_apply_apply (Equiv.optionCongr e) b

private theorem lw_comp_eq_iff {Λ Λ' : Type} (e : Λ ≃ Λ') (x : Option Λ') (k : Option Λ) :
    x = Option.map e k ↔ (Equiv.optionCongr e).symm x = k := by
  constructor
  · intro h
    rw [h]
    exact lw_comp_symm_map e k
  · intro h
    have h2 : Option.map e ((Equiv.optionCongr e).symm x) = Option.map e k := by rw [h]
    rwa [← Equiv.optionCongr_apply, Equiv.apply_symm_apply] at h2

theorem lw_single_comp' {Λ Λ' : Type} [DecidableEq Λ] [DecidableEq Λ']
    (e : Λ ≃ Λ') (k : Option Λ) :
    (Pi.single (Option.map e k) (1 : ℤ) : Option Λ' → ℤ) =
      (Pi.single k (1 : ℤ) : Option Λ → ℤ) ∘ (Equiv.optionCongr e).symm := by
  funext x
  rw [Function.comp_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : x = Option.map e k
  · rw [if_pos h, if_pos ((lw_comp_eq_iff e x k).mp h)]
  · rw [if_neg h, if_neg (fun hk => h ((lw_comp_eq_iff e x k).mpr hk))]

private theorem lw_sRefl_comp {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j)
    (j : Option Λ) (v : Option Λ → ℤ) :
    ggSRefl X' (Option.map e j) (v ∘ (Equiv.optionCongr e).symm) =
      (ggSRefl X j v) ∘ (Equiv.optionCongr e).symm := by
  funext i
  have hrow : (∑ a : Option Λ',
        X' (Option.map e j) a * v ((Equiv.optionCongr e).symm a))
      = ∑ b : Option Λ, X j b * v b := by
    rw [← Equiv.sum_comp (Equiv.optionCongr e)
      (fun a : Option Λ' => X' (Option.map e j) a * v ((Equiv.optionCongr e).symm a))]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Equiv.optionCongr_apply, hX j b, lw_comp_symm_map e b]
  have hsingle : (Pi.single (Option.map e j) (1 : ℤ) : Option Λ' → ℤ) i
      = (Pi.single (M := fun _ => ℤ) j (1 : ℤ) : Option Λ → ℤ)
          ((Equiv.optionCongr e).symm i) := by
    have h := congrFun (lw_single_comp' e j) i
    simpa [Function.comp_def] using h
  simp only [ggSRefl, Pi.sub_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrow, hsingle]

private theorem lw_sReflR_comp {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j)
    (j : Option Λ) (c : Option Λ → ℤ) :
    ggSReflR X' (Option.map e j) (c ∘ (Equiv.optionCongr e).symm) =
      (ggSReflR X j c) ∘ (Equiv.optionCongr e).symm := by
  funext i
  have hcol : (∑ a : Option Λ',
        c ((Equiv.optionCongr e).symm a) * X' a (Option.map e j))
      = ∑ b : Option Λ, c b * X b j := by
    rw [← Equiv.sum_comp (Equiv.optionCongr e)
      (fun a : Option Λ' => c ((Equiv.optionCongr e).symm a) * X' a (Option.map e j))]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Equiv.symm_apply_apply, Equiv.optionCongr_apply, hX b j]
  have hsingle : (Pi.single (Option.map e j) (1 : ℤ) : Option Λ' → ℤ) i
      = (Pi.single (M := fun _ => ℤ) j (1 : ℤ) : Option Λ → ℤ)
          ((Equiv.optionCongr e).symm i) := by
    have h := congrFun (lw_single_comp' e j) i
    simpa [Function.comp_def] using h
  simp only [ggSReflR, Pi.sub_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [hcol, hsingle]

theorem lw_sWord_comp {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j)
    (ψ : List (Option Λ)) (v : Option Λ → ℤ) :
    ggSWord X' (ψ.map (Option.map e)) (v ∘ (Equiv.optionCongr e).symm) =
      (ggSWord X ψ v) ∘ (Equiv.optionCongr e).symm := by
  induction ψ with
  | nil => rfl
  | cons j ψ ih =>
      rw [List.map_cons, show ggSWord X' (Option.map e j :: ψ.map (Option.map e))
            (v ∘ (Equiv.optionCongr e).symm)
          = ggSRefl X' (Option.map e j)
              (ggSWord X' (ψ.map (Option.map e)) (v ∘ (Equiv.optionCongr e).symm)) from rfl,
        ih, lw_sRefl_comp e hX j (ggSWord X ψ v)]
      rfl

theorem lw_sWordR_comp {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j)
    (ψ : List (Option Λ)) (c : Option Λ → ℤ) :
    ggSWordR X' (ψ.map (Option.map e)) (c ∘ (Equiv.optionCongr e).symm) =
      (ggSWordR X ψ c) ∘ (Equiv.optionCongr e).symm := by
  induction ψ with
  | nil => rfl
  | cons j ψ ih =>
      rw [List.map_cons, show ggSWordR X' (Option.map e j :: ψ.map (Option.map e))
            (c ∘ (Equiv.optionCongr e).symm)
          = ggSReflR X' (Option.map e j)
              (ggSWordR X' (ψ.map (Option.map e)) (c ∘ (Equiv.optionCongr e).symm)) from rfl,
        ih, lw_sReflR_comp e hX j (ggSWordR X ψ c)]
      rfl

theorem lw_coroots_mem {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j)
    {v' : Option Λ' → ℤ} (hv : v' ∈ ggLCoroots X') :
    v' ∘ (Equiv.optionCongr e) ∈ ggLCoroots X := by
  obtain ⟨ψ, i, rfl⟩ := hv
  refine ⟨ψ.map e.symm, e.symm i, ?_⟩
  have hmap : ψ.map some = ((ψ.map e.symm).map some).map (Option.map e) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro x _
    simp
  calc (ggSWord X' (ψ.map some) (Pi.single (some i) (1 : ℤ))) ∘ (Equiv.optionCongr e)
      = (ggSWord X' (((ψ.map e.symm).map some).map (Option.map e))
          (Pi.single (Option.map e (some (e.symm i))) (1 : ℤ)))
          ∘ (Equiv.optionCongr e) := by rw [hmap]; congr 2; simp
    _ = ((ggSWord X ((ψ.map e.symm).map some) (Pi.single (some (e.symm i)) (1 : ℤ)))
          ∘ (Equiv.optionCongr e).symm) ∘ (Equiv.optionCongr e) := by
          rw [lw_single_comp' e (some (e.symm i)),
            lw_sWord_comp e hX ((ψ.map e.symm).map some) (Pi.single (some (e.symm i)) (1 : ℤ))]
    _ = ggSWord X ((ψ.map e.symm).map some) (Pi.single (some (e.symm i)) (1 : ℤ)) := by
          rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]


theorem ggAttachCartan_map_equiv {Λ : Type} [DecidableEq Λ] {n : ℕ} (e : Fin n ≃ Λ)
    {C : Matrix Λ Λ ℤ} {C₀ : Matrix (Fin n) (Fin n) ℤ} (hC : ∀ i j, C (e i) (e j) = C₀ i j)
    {c : Λ} {k : Fin n} (hc : c = e k) (i j : Option (Fin n)) :
    ggAttachCartan C c (Option.map e i) (Option.map e j) = ggAttachCartan C₀ k i j := by
  rcases i with _ | i <;> rcases j with _ | j <;>
    simp [hC, hc, e.injective.eq_iff]

@[expose] def ggLWdot (a b : List ℤ) : ℤ := (List.zipWith (· * ·) a b).sum

@[expose] def ggLWnode (n i : ℕ) : Option (Fin n) := if h : i < n then some ⟨i, h⟩ else none

@[expose] def ggLWmat {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ) : List (List ℤ) :=
  (List.range (n + 1)).map fun i => (List.range (n + 1)).map fun j => X (ggLWnode n i) (ggLWnode n
    j)

@[expose] def ggLWmatC {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) : List (List ℤ) :=
  (List.range n).map fun i => (List.range n).map fun j =>
    if hi : i < n then (if hj : j < n then C ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0

@[expose] def ggLWrefl (XL : List (List ℤ)) (j : ℕ) (m : List ℤ) : List ℤ :=
  let s := ggLWdot (XL.getD j []) m
  m.mapIdx fun i x => if i = j then x - s else x

@[expose] def ggLWreflR (XL : List (List ℤ)) (j : ℕ) (c : List ℤ) : List ℤ :=
  let s := ggLWdot c (XL.map fun row => row.getD j 0)
  c.mapIdx fun i x => if i = j then x - s else x

@[expose] def ggLWword (XL : List (List ℤ)) (ψ : List ℕ) (m : List ℤ) : List ℤ :=
  ψ.foldr (fun j m => ggLWrefl XL j m) m

@[expose] def ggLWwordR (XL : List (List ℤ)) (ψ : List ℕ) (c : List ℤ) : List ℤ :=
  ψ.foldr (fun j c => ggLWreflR XL j c) c

@[expose] def ggLWunit (N k : ℕ) : List ℤ := (List.range N).map fun i => if i = k then 1 else 0

@[expose] def ggLWminors (u v : List ℤ) : ℕ :=
  ((List.range u.length).flatMap fun i => (List.range u.length).filterMap fun j =>
    if i < j then some (u.getD i 0 * v.getD j 0 - u.getD j 0 * v.getD i 0).natAbs else none).foldl
      Nat.gcd 0

@[expose] def ggLWdecode (n c : ℕ) : List ℤ :=
  (List.range n).map fun i => ((c / 16 ^ i % 16 : ℕ) : ℤ) - 8

@[expose] def ggLWclosed (XL : List (List ℤ)) (n : ℕ) (R : List (List ℤ)) : Bool :=
  (List.range n).all (fun i => R.contains (ggLWunit n i)) &&
    R.all fun v => (List.range n).all fun j => R.contains (ggLWrefl XL j v)

@[expose] def ggLWdata (XL : List (List ℤ)) (n : ℕ) (R : List (List ℤ)) (ψ₀ : List ℕ) (k₀ : ℕ)
    (ψγ : List ℕ) (kγ : ℕ) : Bool :=
  let N := n + 1
  let g₀ := ggLWword XL ψ₀ (ggLWunit N k₀)
  let c₀ := ggLWwordR XL ψ₀ (ggLWunit N k₀)
  let g := ggLWword XL ψγ (ggLWunit N kγ)
  let cγ := ggLWwordR XL ψγ (ggLWunit N kγ)
  let pair := fun (c m : List ℤ) => ggLWdot c (XL.map fun row => ggLWdot row m)
  let s := c₀.getD n 0 + cγ.getD n 0
  let a₀ := c₀.getD n 0
  let w := List.zipWith (fun x y => (s - a₀) * x - a₀ * y) g₀ g
  decide (ψ₀.all (· ≤ n) = true) && decide (ψγ.all (· ≤ n) = true) && decide (k₀ ≤ n) &&
    decide (kγ ≤ n) && decide (pair c₀ g = -2) && decide (pair cγ g₀ = -2) &&
    decide (s ≠ 0) && decide ((12 : ℤ) % (2 * s) = 0) &&
    R.all fun v => decide ((12 : ℕ) % ggLWminors w (v ++ [0]) = 0)

@[expose] def lw_vecOf {n : ℕ} (l : List ℤ) : Option (Fin n) → ℤ :=
  fun o => l.getD (match o with | none => n | some i => i.1) 0

theorem lw_node {n : ℕ} (l : List ℤ) {i : ℕ} (hi : i ≤ n) :
    lw_vecOf l (ggLWnode n i) = l.getD i 0 := by
  by_cases h : i < n
  · simp only [lw_vecOf, ggLWnode, dif_pos h]
  · have hin : i = n := by omega
    rw [hin]
    simp only [lw_vecOf, ggLWnode, dif_neg (Nat.lt_irrefl n)]

private theorem lw_node_fin {n : ℕ} (i : Fin n) : ggLWnode n i.1 = some i := by
  simp only [ggLWnode]
  rw [dif_pos i.2]

theorem lw_node_some {n : ℕ} (l : List ℤ) (i : Fin n) :
    lw_vecOf l (some i) = l.getD i.1 0 := by
  rw [show some i = ggLWnode n i.1 from (lw_node_fin i).symm, lw_node l (le_of_lt i.2)]

theorem lw_node_none {n : ℕ} (l : List ℤ) :
    lw_vecOf l (none : Option (Fin n)) = l.getD n 0 := rfl

private theorem lw_sum_option_range {n : ℕ} {M : Type} [AddCommMonoid M]
    (f : Option (Fin n) → M) :
    ∑ o : Option (Fin n), f o = ∑ i ∈ Finset.range (n + 1), f (ggLWnode n i) := by
  rw [Fintype.sum_option, Finset.sum_range_succ]
  rw [show ggLWnode n n = none from dif_neg (Nat.lt_irrefl n)]
  have hfin : (∑ i : Fin n, f (some i)) = ∑ i : Fin n, f (ggLWnode n i.1) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show some i = ggLWnode n i.1 from (lw_node_fin i).symm]
  rw [hfin, Fin.sum_univ_eq_sum_range (fun i => f (ggLWnode n i)) n]
  exact add_comm _ _

private theorem lw_row {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ) {j : ℕ}
    (hj : j ≤ n) :
    (ggLWmat X).getD j [] =
      (List.range (n + 1)).map (fun b => X (ggLWnode n j) (ggLWnode n b)) := by
  have hlt : j < (ggLWmat X).length := by
    simp only [ggLWmat, List.length_map, List.length_range]; omega
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [ggLWmat, List.getElem_map, List.getElem_range]

private theorem lw_dot_map {N : ℕ} (fb : ℕ → ℤ) (l : List ℤ) (hl : l.length = N) :
    ggLWdot ((List.range N).map fb) l
      = ∑ b ∈ Finset.range N, fb b * l.getD b 0 := by
  rw [ggLWdot, List.zipWith_map_left]
  have hlist : List.zipWith (fun a b => fb a * b) (List.range N) l
      = List.ofFn (fun i : Fin N => fb i.1 * l.getD i.1 0) := by
    apply List.ext_getElem
    · rw [List.length_zipWith, List.length_range, hl, min_self, List.length_ofFn]
    · intro i h1 h2
      have hi : i < l.length :=
        lt_of_lt_of_le h1 (by rw [List.length_zipWith]; exact min_le_right _ _)
      rw [List.getElem_zipWith, List.getElem_range, List.getElem_ofFn]
      rw [← List.getD_eq_getElem l 0 hi]
  rw [hlist, List.sum_ofFn, Fin.sum_univ_eq_sum_range (fun i => fb i * l.getD i 0) N]

private theorem lw_sRefl_bridge {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    {j : ℕ} (hj : j ≤ n) (l : List ℤ) (hl : l.length = n + 1) :
    ggSRefl X (ggLWnode n j) (lw_vecOf l) = lw_vecOf (ggLWrefl (ggLWmat X) j l) := by
  have hsum : (∑ i : Option (Fin n), X (ggLWnode n j) i * lw_vecOf l i)
      = ∑ b ∈ Finset.range (n + 1), X (ggLWnode n j) (ggLWnode n b) * l.getD b 0 := by
    rw [lw_sum_option_range]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [lw_node l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))]
  have hdot : ggLWdot ((ggLWmat X).getD j []) l
      = ∑ b ∈ Finset.range (n + 1), X (ggLWnode n j) (ggLWnode n b) * l.getD b 0 := by
    rw [lw_row X hj, lw_dot_map _ l hl]
  have hlen : (ggLWrefl (ggLWmat X) j l).length = n + 1 := by
    simp only [ggLWrefl, List.length_mapIdx, hl]
  funext o
  rw [show ggSRefl X (ggLWnode n j) (lw_vecOf l)
      = lw_vecOf l - (∑ i : Option (Fin n), X (ggLWnode n j) i * lw_vecOf l i) •
          Pi.single (ggLWnode n j) 1 from rfl]
  rw [hsum, ← hdot]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rcases o with _ | i
  · rw [lw_node_none,
      show lw_vecOf (ggLWrefl (ggLWmat X) j l) none
        = (ggLWrefl (ggLWmat X) j l).getD n 0 from rfl]
    rw [List.getD_eq_getElem (ggLWrefl (ggLWmat X) j l) 0 (by rw [hlen]; omega)]
    simp only [ggLWrefl, List.getElem_mapIdx]
    rw [← List.getD_eq_getElem l 0 (by omega)]
    by_cases hjn : j = n
    · rw [hjn, show ggLWnode n n = none from dif_neg (Nat.lt_irrefl n)]
      rw [Pi.single_apply, if_pos rfl, if_pos rfl]
      ring
    · have hjs : j < n := lt_of_le_of_ne hj hjn
      rw [show ggLWnode n j = some ⟨j, hjs⟩ from dif_pos hjs]
      rw [Pi.single_apply, if_neg (by simp), mul_zero, sub_zero,
        if_neg (by omega : ¬ n = j)]
  · rw [lw_node_some,
      show lw_vecOf (ggLWrefl (ggLWmat X) j l) (some i)
        = (ggLWrefl (ggLWmat X) j l).getD i.1 0 from rfl]
    rw [List.getD_eq_getElem (ggLWrefl (ggLWmat X) j l) 0 (by rw [hlen]; omega)]
    simp only [ggLWrefl, List.getElem_mapIdx]
    rw [← List.getD_eq_getElem l 0 (by omega)]
    by_cases hjn : j = n
    · rw [hjn, show ggLWnode n n = none from dif_neg (Nat.lt_irrefl n)]
      rw [Pi.single_apply, if_neg (by simp), if_neg (by omega : ¬ i.1 = n)]
      ring
    · have hjs : j < n := lt_of_le_of_ne hj hjn
      rw [show ggLWnode n j = some ⟨j, hjs⟩ from dif_pos hjs]
      rw [Pi.single_apply]
      by_cases hij : i.1 = j
      · rw [if_pos (by simp [Fin.ext_iff, hij]), if_pos hij]; ring
      · rw [if_neg (by simp [Fin.ext_iff, hij]), if_neg hij]; ring


private theorem lw_dot_comm (a b : List ℤ) : ggLWdot a b = ggLWdot b a := by
  induction a generalizing b with
  | nil => cases b <;> simp [ggLWdot]
  | cons x xs ih =>
      cases b with
      | nil => simp [ggLWdot]
      | cons y ys =>
          simp only [ggLWdot, List.zipWith_cons_cons, List.sum_cons]
          rw [show (List.zipWith (fun x1 x2 : ℤ => x1 * x2) xs ys).sum
                = (List.zipWith (fun x1 x2 : ℤ => x1 * x2) ys xs).sum from ih ys]
          ring

theorem lw_word_length {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    (ψ : List ℕ) (l : List ℤ) : (ggLWword (ggLWmat X) ψ l).length = l.length := by
  induction ψ with
  | nil => rfl
  | cons j ψ ih =>
      show (ggLWrefl (ggLWmat X) j (ggLWword (ggLWmat X) ψ l)).length = l.length
      simp only [ggLWrefl, List.length_mapIdx]
      exact ih

theorem lw_wordR_length {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    (ψ : List ℕ) (l : List ℤ) : (ggLWwordR (ggLWmat X) ψ l).length = l.length := by
  induction ψ with
  | nil => rfl
  | cons j ψ ih =>
      show (ggLWreflR (ggLWmat X) j (ggLWwordR (ggLWmat X) ψ l)).length = l.length
      simp only [ggLWreflR, List.length_mapIdx]
      exact ih

private theorem lw_sReflR_bridge {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    {j : ℕ} (hj : j ≤ n) (c : List ℤ) (hc : c.length = n + 1) :
    ggSReflR X (ggLWnode n j) (lw_vecOf c) = lw_vecOf (ggLWreflR (ggLWmat X) j c) := by
  have hcol : (∑ i : Option (Fin n), lw_vecOf c i * X i (ggLWnode n j))
      = ∑ b ∈ Finset.range (n + 1), c.getD b 0 * X (ggLWnode n b) (ggLWnode n j) := by
    rw [lw_sum_option_range]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [lw_node c (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))]
  have hmap : (ggLWmat X).map (fun row => row.getD j 0)
      = (List.range (n + 1)).map (fun b => X (ggLWnode n b) (ggLWnode n j)) := by
    simp only [ggLWmat, List.map_map]
    apply List.map_congr_left
    intro a _
    change ((List.range (n + 1)).map (fun b => X (ggLWnode n a) (ggLWnode n b))).getD j 0
      = X (ggLWnode n a) (ggLWnode n j)
    have hlt : j < ((List.range (n + 1)).map (fun b => X (ggLWnode n a) (ggLWnode n b))).length :=
      by
      simp only [List.length_map, List.length_range]; omega
    rw [List.getD_eq_getElem _ _ hlt, List.getElem_map, List.getElem_range]
  have hdot : ggLWdot c ((ggLWmat X).map (fun row => row.getD j 0))
      = ∑ b ∈ Finset.range (n + 1), c.getD b 0 * X (ggLWnode n b) (ggLWnode n j) := by
    rw [hmap, lw_dot_comm, lw_dot_map _ c hc]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  have hlen : (ggLWreflR (ggLWmat X) j c).length = n + 1 := by
    simp only [ggLWreflR, List.length_mapIdx, hc]
  funext o
  rw [show ggSReflR X (ggLWnode n j) (lw_vecOf c)
      = lw_vecOf c - (∑ i : Option (Fin n), lw_vecOf c i * X i (ggLWnode n j)) •
          Pi.single (ggLWnode n j) 1 from rfl]
  rw [hcol, ← hdot]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rcases o with _ | i
  · rw [lw_node_none,
      show lw_vecOf (ggLWreflR (ggLWmat X) j c) none
        = (ggLWreflR (ggLWmat X) j c).getD n 0 from rfl]
    rw [List.getD_eq_getElem (ggLWreflR (ggLWmat X) j c) 0 (by rw [hlen]; omega)]
    simp only [ggLWreflR, List.getElem_mapIdx]
    rw [← List.getD_eq_getElem c 0 (by omega)]
    by_cases hjn : j = n
    · rw [hjn, show ggLWnode n n = none from dif_neg (Nat.lt_irrefl n)]
      rw [Pi.single_apply, if_pos rfl, if_pos rfl]
      ring
    · have hjs : j < n := lt_of_le_of_ne hj hjn
      rw [show ggLWnode n j = some ⟨j, hjs⟩ from dif_pos hjs]
      rw [Pi.single_apply, if_neg (by simp), mul_zero, sub_zero,
        if_neg (by omega : ¬ n = j)]
  · rw [lw_node_some,
      show lw_vecOf (ggLWreflR (ggLWmat X) j c) (some i)
        = (ggLWreflR (ggLWmat X) j c).getD i.1 0 from rfl]
    rw [List.getD_eq_getElem (ggLWreflR (ggLWmat X) j c) 0 (by rw [hlen]; omega)]
    simp only [ggLWreflR, List.getElem_mapIdx]
    rw [← List.getD_eq_getElem c 0 (by omega)]
    by_cases hjn : j = n
    · rw [hjn, show ggLWnode n n = none from dif_neg (Nat.lt_irrefl n)]
      rw [Pi.single_apply, if_neg (by simp), if_neg (by omega : ¬ i.1 = n)]
      ring
    · have hjs : j < n := lt_of_le_of_ne hj hjn
      rw [show ggLWnode n j = some ⟨j, hjs⟩ from dif_pos hjs]
      rw [Pi.single_apply]
      by_cases hij : i.1 = j
      · rw [if_pos (by simp [Fin.ext_iff, hij]), if_pos hij]; ring
      · rw [if_neg (by simp [Fin.ext_iff, hij]), if_neg hij]; ring


theorem lw_sWord_bridge {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    (ψ : List ℕ) (hψ : ∀ j ∈ ψ, j ≤ n) (l : List ℤ) (hl : l.length = n + 1) :
    ggSWord X (ψ.map (ggLWnode n)) (lw_vecOf l) = lw_vecOf (ggLWword (ggLWmat X) ψ l) := by
  induction ψ generalizing l with
  | nil => rfl
  | cons j ψ ih =>
      have hj : j ≤ n := hψ j (by simp)
      have hψ' : ∀ t ∈ ψ, t ≤ n := fun t ht => hψ t (by simp [ht])
      show ggSRefl X (ggLWnode n j) (ggSWord X (ψ.map (ggLWnode n)) (lw_vecOf l))
        = lw_vecOf (ggLWrefl (ggLWmat X) j (ggLWword (ggLWmat X) ψ l))
      rw [ih hψ' l hl,
        lw_sRefl_bridge X hj (ggLWword (ggLWmat X) ψ l) (by rw [lw_word_length, hl])]

theorem lw_sWordR_bridge {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    (ψ : List ℕ) (hψ : ∀ j ∈ ψ, j ≤ n) (l : List ℤ) (hl : l.length = n + 1) :
    ggSWordR X (ψ.map (ggLWnode n)) (lw_vecOf l)
      = lw_vecOf (ggLWwordR (ggLWmat X) ψ l) := by
  induction ψ generalizing l with
  | nil => rfl
  | cons j ψ ih =>
      have hj : j ≤ n := hψ j (by simp)
      have hψ' : ∀ t ∈ ψ, t ≤ n := fun t ht => hψ t (by simp [ht])
      show ggSReflR X (ggLWnode n j) (ggSWordR X (ψ.map (ggLWnode n)) (lw_vecOf l))
        = lw_vecOf (ggLWreflR (ggLWmat X) j (ggLWwordR (ggLWmat X) ψ l))
      rw [ih hψ' l hl,
        lw_sReflR_bridge X hj (ggLWwordR (ggLWmat X) ψ l) (by rw [lw_wordR_length, hl])]

private theorem lw_unit_succ {n k : ℕ} (hk : k < n) :
    ggLWunit (n + 1) k = ggLWunit n k ++ [0] := by
  simp only [ggLWunit, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  rw [if_neg (by omega : ¬ n = k)]

private theorem lw_node_inj {n t k : ℕ} (ht : t ≤ n) (hk : k ≤ n)
    (h : ggLWnode n t = ggLWnode n k) : t = k := by
  by_cases ht' : t < n
  · rw [show ggLWnode n t = some ⟨t, ht'⟩ from dif_pos ht'] at h
    by_cases hk' : k < n
    · rw [show ggLWnode n k = some ⟨k, hk'⟩ from dif_pos hk'] at h
      exact congrArg Fin.val (Option.some.inj h)
    · rw [show ggLWnode n k = none from dif_neg hk'] at h
      exact absurd h (by simp)
  · have htn : t = n := le_antisymm ht (le_of_not_gt ht')
    by_cases hk' : k < n
    · rw [show ggLWnode n t = none from dif_neg ht',
        show ggLWnode n k = some ⟨k, hk'⟩ from dif_pos hk'] at h
      exact absurd h (by simp)
    · have hkn : k = n := le_antisymm hk (le_of_not_gt hk')
      omega

private theorem lw_unit_bridge_point {n : ℕ} (k : ℕ) (hk : k ≤ n) {t : ℕ} (ht : t ≤ n) :
    lw_vecOf (ggLWunit (n + 1) k) (ggLWnode n t)
      = (Pi.single (ggLWnode n k) (1 : ℤ) : Option (Fin n) → ℤ) (ggLWnode n t) := by
  rw [lw_node (ggLWunit (n + 1) k) ht, Pi.single_apply]
  have hone : (ggLWunit (n + 1) k).getD t 0 = if t = k then (1 : ℤ) else 0 := by
    simp only [ggLWunit]
    rw [List.getD_eq_getElem _ _ (by simp [List.length_map, List.length_range]; omega)]
    rw [List.getElem_map, List.getElem_range]
  rw [hone]
  by_cases htk : t = k
  · rw [if_pos htk, if_pos (by rw [htk])]
  · rw [if_neg htk, if_neg (fun h => htk (lw_node_inj ht hk h))]

theorem lw_unit_bridge {n : ℕ} (k : ℕ) (hk : k ≤ n) :
    lw_vecOf (ggLWunit (n + 1) k) = (Pi.single (ggLWnode n k) (1 : ℤ) : Option (Fin n) → ℤ) := by
  funext o
  rcases o with _ | i
  · rw [← show ggLWnode n n = none from dif_neg (Nat.lt_irrefl n)]
    exact lw_unit_bridge_point k hk (le_refl n)
  · rw [← lw_node_fin i]
    exact lw_unit_bridge_point k hk (le_of_lt i.2)

private theorem lw_rowC {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) {j : ℕ} (hj : j < n) :
    (ggLWmatC C).getD j [] =
      (List.range n).map (fun b => if hb : b < n then C ⟨j, hj⟩ ⟨b, hb⟩ else 0) := by
  have hlt : j < (ggLWmatC C).length := by
    simp only [ggLWmatC, List.length_map, List.length_range]; omega
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [ggLWmatC, List.getElem_map, List.getElem_range]
  simp only [dif_pos hj]


private theorem lw_attach_sRefl_bridge {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (k : Fin n)
    {j : ℕ} (hj : j < n) (v : List ℤ) (hv : v.length = n) :
    ggSRefl (ggAttachCartan C k) (ggLWnode n j) (lw_vecOf (v ++ [0]))
      = lw_vecOf (ggLWrefl (ggLWmatC C) j v ++ [0]) := by
  have hdot : ggLWdot ((ggLWmatC C).getD j []) v
      = ∑ b ∈ Finset.range n, (if hb : b < n then C ⟨j, hj⟩ ⟨b, hb⟩ else 0) * v.getD b 0 := by
    rw [lw_rowC C hj, lw_dot_map (fun b => if hb : b < n then C ⟨j, hj⟩ ⟨b, hb⟩ else 0) v (by rw
      [hv])]
  have hsum : (∑ o : Option (Fin n),
        ggAttachCartan C k (ggLWnode n j) o * lw_vecOf (v ++ [0]) o)
      = ggLWdot ((ggLWmatC C).getD j []) v := by
    rw [Fintype.sum_option]
    have hnone : ggAttachCartan C k (ggLWnode n j) (none : Option (Fin n))
        * lw_vecOf (v ++ [0]) (none : Option (Fin n)) = 0 := by
      rw [lw_node_none]
      have h0 : (v ++ [0]).getD n 0 = (0 : ℤ) := by
        rw [List.getD_append_right v [0] 0 n (by rw [hv])]
        simp
      rw [h0, mul_zero]
    rw [hnone, zero_add]
    have hsome : (∑ i : Fin n, ggAttachCartan C k (ggLWnode n j) (some i)
          * lw_vecOf (v ++ [0]) (some i))
        = ∑ i : Fin n, C ⟨j, hj⟩ i * v.getD i.1 0 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show ggLWnode n j = some ⟨j, hj⟩ from dif_pos hj, ggAttachCartan_some_some,
        lw_node_some]
      congr 1
      rw [List.getD_append v [0] 0 i.1 (by rw [hv]; exact i.2)]
    rw [hsome, hdot]
    have hF : (∑ i : Fin n, C ⟨j, hj⟩ i * v.getD i.1 0)
        = ∑ i : Fin n,
            (if hb : i.1 < n then C ⟨j, hj⟩ ⟨i.1, hb⟩ * v.getD i.1 0 else 0) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [dif_pos i.2]
    rw [hF, Fin.sum_univ_eq_sum_range
      (fun b => if hb : b < n then C ⟨j, hj⟩ ⟨b, hb⟩ * v.getD b 0 else 0) n]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb : b < n
    · simp only [dif_pos hb]
    · simp only [dif_neg hb, zero_mul]
  have hlen : (ggLWrefl (ggLWmatC C) j v).length = n := by
    simp only [ggLWrefl, List.length_mapIdx, hv]
  rw [show ggSRefl (ggAttachCartan C k) (ggLWnode n j) (lw_vecOf (v ++ [0]))
      = lw_vecOf (v ++ [0]) - (∑ o : Option (Fin n),
          ggAttachCartan C k (ggLWnode n j) o * lw_vecOf (v ++ [0]) o) •
          Pi.single (ggLWnode n j) 1 from rfl, hsum]
  funext o
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rcases o with _ | i
  · rw [lw_node_none]
    have h0 : (v ++ [0]).getD n 0 = (0 : ℤ) := by
      rw [List.getD_append_right v [0] 0 n (by rw [hv])]
      simp
    rw [show ggLWnode n j = some ⟨j, hj⟩ from dif_pos hj,
      Pi.single_apply, if_neg (fun h => by cases h)]
    rw [h0, mul_zero, sub_zero]
    rw [lw_node_none,
      List.getD_append_right (ggLWrefl (ggLWmatC C) j v) [0] 0 n (by rw [hlen])]
    simp
  · rw [lw_node_some,
      show ggLWnode n j = some ⟨j, hj⟩ from dif_pos hj, Pi.single_apply]
    rw [List.getD_append v [0] 0 i.1 (by rw [hv]; exact i.2)]
    rw [show lw_vecOf (ggLWrefl (ggLWmatC C) j v ++ [0]) (some i)
        = (ggLWrefl (ggLWmatC C) j v ++ [0]).getD i.1 0 from rfl]
    rw [List.getD_append (ggLWrefl (ggLWmatC C) j v) [0] 0 i.1 (by rw [hlen]; exact i.2)]
    have hr : (ggLWrefl (ggLWmatC C) j v).getD i.1 0
        = if i.1 = j then v.getD i.1 0 - ggLWdot ((ggLWmatC C).getD j []) v
          else v.getD i.1 0 := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact i.2)]
      simp only [ggLWrefl, List.getElem_mapIdx]
      rw [← List.getD_eq_getElem v 0 (by rw [hv]; exact i.2)]
    rw [hr]
    by_cases hij : i.1 = j
    · rw [if_pos hij, if_pos (by simp [Fin.ext_iff, hij])]; ring
    · rw [if_neg hij, if_neg (by simp [Fin.ext_iff, hij])]; ring


theorem lw_mem_R {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) (R : List (List ℤ))
    (hclosed : ggLWclosed (ggLWmatC C) n R = true) :
    ∀ v ∈ ggLCoroots (ggAttachCartan C k),
      ∃ l ∈ R, l.length = n ∧ v = lw_vecOf (l ++ [0]) := by
  have hcl := hclosed
  simp only [ggLWclosed, Bool.and_eq_true, List.all_eq_true] at hcl
  obtain ⟨hunit, hrefl⟩ := hcl
  intro v hv
  obtain ⟨ψ, i, rfl⟩ := hv
  induction ψ with
  | nil =>
      refine ⟨ggLWunit n i.1, ?_, ?_, ?_⟩
      · exact List.contains_iff_mem.mp (hunit i.1 (List.mem_range.mpr i.2))
      · simp only [ggLWunit, List.length_map, List.length_range]
      · rw [← lw_unit_succ i.2, lw_unit_bridge i.1 (le_of_lt i.2), lw_node_fin i]
        rfl
  | cons j ψ ih =>
      obtain ⟨l, hlR, hll, hleq⟩ := ih
      refine ⟨ggLWrefl (ggLWmatC C) j.1 l, ?_, ?_, ?_⟩
      · exact List.contains_iff_mem.mp (hrefl l hlR j.1 (List.mem_range.mpr j.2))
      · simp only [ggLWrefl, List.length_mapIdx, hll]
      · rw [show ggSWord (ggAttachCartan C k) ((j :: ψ).map some) (Pi.single (some i) 1)
            = ggSRefl (ggAttachCartan C k) (some j)
                (ggSWord (ggAttachCartan C k) (ψ.map some) (Pi.single (some i) 1)) from rfl,
          hleq, show some j = ggLWnode n j.1 from (lw_node_fin j).symm,
          lw_attach_sRefl_bridge C k j.2 l hll]


theorem lw_pair_bridge {n : ℕ} (X : Matrix (Option (Fin n)) (Option (Fin n)) ℤ)
    (cL gL : List ℤ) (hc : cL.length = n + 1) (hg : gL.length = n + 1) :
    (∑ i : Option (Fin n), ∑ j : Option (Fin n), lw_vecOf cL i * X i j * lw_vecOf gL j)
      = ggLWdot cL ((ggLWmat X).map fun row => ggLWdot row gL) := by
  have hL : (∑ i : Option (Fin n), ∑ j : Option (Fin n),
        lw_vecOf cL i * X i j * lw_vecOf gL j)
      = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
          cL.getD a 0 * X (ggLWnode n a) (ggLWnode n b) * gL.getD b 0 := by
    rw [lw_sum_option_range]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [lw_sum_option_range]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [lw_node cL (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)),
      lw_node gL (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))]
  have hR : ggLWdot cL ((ggLWmat X).map fun row => ggLWdot row gL)
      = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
          cL.getD a 0 * X (ggLWnode n a) (ggLWnode n b) * gL.getD b 0 := by
    have hmap : (ggLWmat X).map (fun row => ggLWdot row gL)
        = (List.range (n + 1)).map (fun a => ggLWdot ((List.range (n + 1)).map
            (fun b => X (ggLWnode n a) (ggLWnode n b))) gL) := by
      simp only [ggLWmat, List.map_map, Function.comp_def]
    rw [lw_dot_comm, hmap,
      lw_dot_map (fun a => ggLWdot ((List.range (n + 1)).map
        (fun b => X (ggLWnode n a) (ggLWnode n b))) gL) cL hc]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [lw_dot_map (fun b => X (ggLWnode n a) (ggLWnode n b)) gL hg, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hL, hR]

theorem lw_zipWith_getD_of_lt (f : ℤ → ℤ → ℤ) (a b : List ℤ) {t : ℕ}
    (ha : t < a.length) (hb : t < b.length) :
    (List.zipWith f a b).getD t 0 = f (a.getD t 0) (b.getD t 0) := by
  have ht : t < (List.zipWith f a b).length := by
    rw [List.length_zipWith]; exact lt_min ha hb
  rw [List.getD_eq_getElem _ _ ht, List.getElem_zipWith,
    ← List.getD_eq_getElem a 0 ha, ← List.getD_eq_getElem b 0 hb]

theorem lw_w_point {n : ℕ} (g₀ g w : List ℤ) (s a₀ : ℤ)
    (hw : w = List.zipWith (fun x y => (s - a₀) * x - a₀ * y) g₀ g)
    (hg₀ : g₀.length = n + 1) (hg : g.length = n + 1) {t : ℕ} (ht : t ≤ n) :
    w.getD t 0 = (s - a₀) * g₀.getD t 0 - a₀ * g.getD t 0 := by
  subst hw
  rw [lw_zipWith_getD_of_lt (fun x y => (s - a₀) * x - a₀ * y) g₀ g
    (by omega) (by omega)]

private theorem lw_dvd_foldl_gcd {p : ℕ} (l : List ℕ) {acc : ℕ} (hacc : p ∣ acc)
    (h : ∀ m ∈ l, p ∣ m) : p ∣ l.foldl Nat.gcd acc := by
  induction l generalizing acc with
  | nil => simpa using hacc
  | cons a t ih =>
      rw [List.foldl_cons]
      exact ih (Nat.dvd_gcd hacc (h a (by simp))) (fun m hm => h m (by simp [hm]))

private theorem lw_natAbs_dvd_of_int_dvd {p : ℕ} {x : ℤ} (h : (p : ℤ) ∣ x) : p ∣ x.natAbs := by
  have h' := Int.natAbs_dvd_natAbs.mpr h
  rwa [Int.natAbs_natCast] at h'

theorem lw_minors_dvd_of_minors {p : ℕ} {u v : List ℤ}
    (h : ∀ i j, i < u.length → j < u.length → i < j →
        (p : ℤ) ∣ (u.getD i 0 * v.getD j 0 - u.getD j 0 * v.getD i 0)) :
    p ∣ ggLWminors u v := by
  rw [ggLWminors]
  refine lw_dvd_foldl_gcd (p := p) (l := (List.range u.length).flatMap fun i =>
      (List.range u.length).filterMap fun j =>
        if i < j then some (u.getD i 0 * v.getD j 0 - u.getD j 0 * v.getD i 0).natAbs else none)
    (acc := 0) (Nat.dvd_zero p) ?_
  intro m hm
  rw [List.mem_flatMap] at hm
  obtain ⟨i, hi, hm⟩ := hm
  rw [List.mem_filterMap] at hm
  obtain ⟨j, hj, hsome⟩ := hm
  by_cases hij : i < j
  · rw [if_pos hij] at hsome
    rw [← Option.some.inj hsome]
    exact lw_natAbs_dvd_of_int_dvd (h i j (List.mem_range.mp hi) (List.mem_range.mp hj) hij)
  · rw [if_neg hij] at hsome
    exact absurd hsome (by simp)

theorem lw_prime_not_dvd_12 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ¬ p ∣ 12 := by
  intro h
  have h' : p ∣ 2 * (2 * 3) := by rwa [show 2 * (2 * 3) = 12 by norm_num]
  rcases hp.dvd_mul.mp h' with h2 | h6
  · have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  · rcases hp.dvd_mul.mp h6 with h2 | h3
    · have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      omega
    · have : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
      omega

theorem lw_h2ms_identity {R : Type} [CommRing R] {s a₀ : ℤ} {m : ℕ}
    (h2ms : (2 : R) * (m : R) * (s : R) = (a₀ : R)) (x y : R) :
    (s : R) * (x - (2 : R) * (m : R) * (x + y)) = (s - a₀) * x - a₀ * y := by
  rw [← h2ms]
  ring


end CFSG.StandardType
