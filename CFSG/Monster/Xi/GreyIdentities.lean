module

public import CFSG.Monster.Xi.Grey
public import CFSG.Monster.Lagrangian
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.Monster.Xi

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin

private theorem zmod2_add_self' : ∀ c : ZMod 2, c + c = 0 := by decide

private theorem forall_fin6 {P : (Fin 6 → ZMod 2) → Prop}
    (h : ∀ a b c d e f : ZMod 2, P ![a, b, c, d, e, f]) : ∀ μ, P μ := by
  intro μ
  have hμ : μ = ![μ 0, μ 1, μ 2, μ 3, μ 4, μ 5] := by
    funext i; fin_cases i <;> rfl
  rw [hμ]
  exact h _ _ _ _ _ _

private theorem qG_add_aux : ∀ a b c d e f a' b' c' d' e' f' : ZMod 2,
    qG (![a, b, c, d, e, f] + ![a', b', c', d', e', f']) =
      qG ![a, b, c, d, e, f] + qG ![a', b', c', d', e', f'] +
        bG ![a, b, c, d, e, f] ![a', b', c', d', e', f'] := by
  decide +kernel

theorem qG_add (μ ν : Fin 6 → ZMod 2) : qG (μ + ν) = qG μ + qG ν + bG μ ν := by
  revert μ ν
  exact forall_fin6 fun a b c d e f => forall_fin6 fun a' b' c' d' e' f' =>
    qG_add_aux a b c d e f a' b' c' d' e' f'


theorem bG_comm (μ ν : Fin 6 → ZMod 2) : bG μ ν = bG ν μ := by
  rw [bG_apply, bG_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i = j
  · subst h; simp
  · rw [ite_eq_left (Ne.symm h), ite_eq_left h, mul_comm]


@[simp] theorem qG_zero : qG 0 = 0 := rfl


theorem pair_greyC_eq_sum (μ : Fin 6 → ZMod 2) (δ : Cocode) :
    pair (greyC μ) δ = ∑ i, μ i * pair ⟨g i, g_mem_C i⟩ δ := by
  induction δ using Submodule.Quotient.induction_on with
  | H x =>
    simp only [pair_mk, coe_greyC, sum_dotProduct, smul_dotProduct, smul_eq_mul]

private def M6 (x : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 := fun i => ∑ j, if i ≠ j then x j else 0

private theorem M6_M6_aux : ∀ a b c d e f : ZMod 2, M6 (M6 ![a, b, c, d, e, f]) = ![a, b, c, d, e, f] := by
  decide +kernel

private theorem M6_M6 (x : Fin 6 → ZMod 2) : M6 (M6 x) = x :=
  forall_fin6 (P := fun x => M6 (M6 x) = x) M6_M6_aux x

private theorem bG_eq_sum_M6 (μ ν : Fin 6 → ZMod 2) : bG μ ν = ∑ i, μ i * M6 ν i := by
  rw [bG_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [M6, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem exists_gammaD_add_mem_Hstar (δ : Cocode) :
    ∃ ν : Fin 6 → ZMod 2, δ - gammaD ν ∈ Hstar := by
  set p : Fin 6 → ZMod 2 := fun i => pair ⟨g i, g_mem_C i⟩ δ
  refine ⟨M6 p, mem_Hstar_iff.2 fun μ => ?_⟩
  rw [map_sub, pair_greyC_gammaD, bG_eq_sum_M6, M6_M6, pair_greyC_eq_sum, sub_self]


theorem disjoint_Gstar_Hstar : Disjoint Gstar Hstar := by
  rw [Submodule.disjoint_def]
  intro δ hδ hH
  rw [← range_gammaD] at hδ
  obtain ⟨ν, rfl⟩ := hδ
  have : ν = 0 := bG_eq_zero_of_forall fun μ => by
    rw [← pair_greyC_gammaD]
    exact mem_Hstar_iff.1 hH μ
  rw [this, map_zero]


theorem pair_H_Gstar {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) {δ : Cocode} (hδ : δ ∈ Gstar) :
    pair h δ = 0 := by
  obtain ⟨y, -, hy⟩ := hh
  have hle : Gstar ≤ LinearMap.ker (pair h) := by
    rw [Gstar, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, pair_mk, γ, dotProduct_single, mul_one, ← hy,
      l_row_zero]
  exact hle hδ

theorem pair_H_gammaD {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) (ν : Fin 6 → ZMod 2) :
    pair h (gammaD ν) = 0 :=
  pair_H_Gstar hh (gammaD_mem_Gstar ν)

private theorem g_lower : ∀ (i j : Fin 6) (r : Fin 4), r ≠ 0 →
    g i (coord r j) = if i = j then 1 else 0 := by
  decide +kernel

theorem coe_greyC_lower (μ : Fin 6 → ZMod 2) (j : Fin 6) {r : Fin 4} (hr : r ≠ 0) :
    (greyC μ : Fin 24 → ZMod 2) (coord r j) = μ j := by
  rw [coe_greyC, Finset.sum_apply]
  simp only [Pi.smul_apply, g_lower _ _ _ hr, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

@[expose] def lowerPairs : Set Cocode :=
  {δ | ∃ (j : Fin 6) (r s : Fin 4), r ≠ 0 ∧ s ≠ 0 ∧ r ≠ s ∧
    δ = Submodule.Quotient.mk (Pi.single (coord r j) 1 + Pi.single (coord s j) 1)}

theorem lowerPairs_subset_Hstar : lowerPairs ⊆ Hstar := by
  rintro _ ⟨j, r, s, hr, hs, -, rfl⟩
  refine mem_Hstar_iff.2 fun μ => ?_
  rw [pair_mk, dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one,
    coe_greyC_lower μ j hr, coe_greyC_lower μ j hs]
  exact zmod2_add_self' _

private theorem single_lower : ∀ j : Fin 6,
    Pi.single (coord 1 j) 1 = g j + greyGamma (fun k => if k = j then 0 else 1) +
      (Pi.single (coord 2 j) 1 + Pi.single (coord 3 j) 1) ∧
    Pi.single (coord 2 j) 1 = g j + greyGamma (fun k => if k = j then 0 else 1) +
      (Pi.single (coord 1 j) 1 + Pi.single (coord 3 j) 1) ∧
    Pi.single (coord 3 j) 1 = g j + greyGamma (fun k => if k = j then 0 else 1) +
      (Pi.single (coord 1 j) 1 + Pi.single (coord 2 j) 1) := by
  decide +kernel

private theorem mk_single_mem (i : Fin 24) :
    Submodule.Quotient.mk (p := C) (Pi.single i 1) ∈ Gstar ⊔ Submodule.span (ZMod 2) lowerPairs := by
  have hlow : ∀ (j : Fin 6) (r s : Fin 4), r ≠ 0 → s ≠ 0 → r ≠ s →
      Submodule.Quotient.mk (p := C) (Pi.single (coord r j) 1 + Pi.single (coord s j) 1) ∈
        Gstar ⊔ Submodule.span (ZMod 2) lowerPairs := fun j r s hr hs hrs =>
    Submodule.mem_sup_right (Submodule.subset_span ⟨j, r, s, hr, hs, hrs, rfl⟩)
  have hg : ∀ (j : Fin 6) (x : Fin 24 → ZMod 2),
      Submodule.Quotient.mk (p := C) x ∈ Gstar ⊔ Submodule.span (ZMod 2) lowerPairs →
      Submodule.Quotient.mk (p := C) (g j + greyGamma (fun k => if k = j then 0 else 1) + x) ∈
        Gstar ⊔ Submodule.span (ZMod 2) lowerPairs := by
    intro j x hx
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add,
      (Submodule.Quotient.mk_eq_zero C).2 (g_mem_C j), zero_add]
    rw [mk_greyGamma]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (gammaD_mem_Gstar _)) hx
  rw [← coord_row_col i]
  generalize row i = r, col i = j
  fin_cases r
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩)
  · change Submodule.Quotient.mk (Pi.single (coord 1 j) 1) ∈ _
    rw [(single_lower j).1]
    exact hg j _ (hlow j 2 3 (by decide) (by decide) (by decide))
  · change Submodule.Quotient.mk (Pi.single (coord 2 j) 1) ∈ _
    rw [(single_lower j).2.1]
    exact hg j _ (hlow j 1 3 (by decide) (by decide) (by decide))
  · change Submodule.Quotient.mk (Pi.single (coord 3 j) 1) ∈ _
    rw [(single_lower j).2.2]
    exact hg j _ (hlow j 1 2 (by decide) (by decide) (by decide))

theorem Gstar_sup_span_lowerPairs : Gstar ⊔ Submodule.span (ZMod 2) lowerPairs = ⊤ := by
  refine eq_top_iff.2 fun δ _ => ?_
  induction δ using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Finset.univ_sum_single x, ← Submodule.mkQ_apply, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hi : Pi.single i (x i) = x i • Pi.single i (1 : ZMod 2) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    rw [hi, map_smul, Submodule.mkQ_apply]
    exact Submodule.smul_mem _ _ (mk_single_mem i)

theorem Hstar_eq_span : Hstar = Submodule.span (ZMod 2) lowerPairs := by
  refine le_antisymm (fun δ hδ => ?_) (Submodule.span_le.2 lowerPairs_subset_Hstar)
  have hspan : Submodule.span (ZMod 2) lowerPairs ≤ Hstar :=
    Submodule.span_le.2 lowerPairs_subset_Hstar
  have hδ' : δ ∈ Gstar ⊔ Submodule.span (ZMod 2) lowerPairs := by
    rw [Gstar_sup_span_lowerPairs]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hδ'
  have hxH : x ∈ Hstar := by
    have := Hstar.sub_mem hδ (hspan hy)
    rwa [add_sub_cancel_right] at this
  have hx0 : x = 0 := (Submodule.disjoint_def.1 disjoint_Gstar_Hstar) x hx hxH
  rw [hx0, zero_add]
  exact hy


end CFSG.Monster.Xi
