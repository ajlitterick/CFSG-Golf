module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitLift

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix CFSG.LieType.CentralExt CFSG.LieType.Universal.Spin

variable {r : ℕ} {k : Type} [Field k]

section Diag

@[expose] def simpleDiag (i : Fin r) (c : kˣ) : Fin r → kˣ :=
  if h : i.val + 1 < r then Pi.mulSingle i c * Pi.mulSingle ⟨i.val + 1, h⟩ c⁻¹
  else if h' : 1 ≤ i.val then Pi.mulSingle ⟨i.val - 1, by omega⟩ c * Pi.mulSingle i c else 1

theorem simpleDiag_apply (i : Fin r) (c : kˣ) (j : Fin r) :
    simpleDiag i c j =
      if i.val + 1 < r then
        (if j.val = i.val then c else 1) * (if j.val = i.val + 1 then c⁻¹ else 1)
      else if 1 ≤ i.val then (if j.val = i.val - 1 then c else 1) * (if j.val = i.val then c else 1)
      else 1 := by
  unfold simpleDiag
  by_cases h : i.val + 1 < r
  · simp [h, Pi.mulSingle_apply, Fin.ext_iff]
  · by_cases h' : 1 ≤ i.val
    · simp [h, h', Pi.mulSingle_apply, Fin.ext_iff]
    · simp [h, h']

theorem simpleDiag_apply_eq_one {i j : Fin r} (c : kˣ)
    (h1 : i.val + 1 < r → j.val ≠ i.val ∧ j.val ≠ i.val + 1)
    (h2 : ¬i.val + 1 < r → 1 ≤ i.val → j.val ≠ i.val - 1 ∧ j.val ≠ i.val) :
    simpleDiag i c j = 1 := by
  rw [simpleDiag_apply]
  by_cases h : i.val + 1 < r
  · obtain ⟨ha, hb⟩ := h1 h
    simp [h, ha, hb]
  · by_cases h' : 1 ≤ i.val
    · obtain ⟨ha, hb⟩ := h2 h h'
      simp [h, h', ha, hb]
    · simp [h, h']

theorem simpleDiag_apply_self_of_lt {i : Fin r} (h : i.val + 1 < r) (c : kˣ) :
    simpleDiag i c i = c := by
  rw [simpleDiag_apply]
  simp [h]

theorem simpleDiag_apply_succ {i j : Fin r} (h : i.val + 1 = j.val) (c : kˣ) :
    simpleDiag i c j = c⁻¹ := by
  rw [simpleDiag_apply, ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h.symm,
    one_mul]

theorem simpleDiag_apply_last {i j : Fin r} (h : i.val + 1 = r) (h1 : 1 ≤ i.val)
    (hj : j.val + 1 = i.val ∨ j.val = i.val) (c : kˣ) : simpleDiag i c j = c := by
  rw [simpleDiag_apply, ite_eq_right (by omega), ite_eq_left h1]
  rcases hj with hj | hj
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), mul_one]
  · rw [ite_eq_right (by omega), ite_eq_left hj, one_mul]

theorem prod_simpleDiag_zero (hr : 3 ≤ r) (u : Fin r → kˣ) (z : Fin r) (hz : z.val = 0) :
    (∏ i, simpleDiag i (u i)) z = u z := by
  rw [Finset.prod_apply, Finset.prod_eq_single z]
  · exact simpleDiag_apply_self_of_lt (by omega) _
  · intro i _ hi
    have hi' : i.val ≠ z.val := fun h => hi (Fin.ext h)
    exact simpleDiag_apply_eq_one _ (fun _ => ⟨by omega, by omega⟩)
      (fun _ _ => ⟨by omega, by omega⟩)
  · simp

theorem prod_simpleDiag_mid (u : Fin r → kˣ) (j p : Fin r) (hp : p.val + 1 = j.val)
    (hj' : j.val + 3 ≤ r) :
    (∏ i, simpleDiag i (u i)) j = (u p)⁻¹ * u j := by
  have hpj : p ≠ j := fun h => by rw [h] at hp; omega
  rw [Finset.prod_apply, Finset.prod_eq_mul p j hpj]
  · rw [simpleDiag_apply_succ hp, simpleDiag_apply_self_of_lt (by omega)]
  · intro i _ ⟨hi1, hi2⟩
    have hi1' : i.val ≠ p.val := fun h => hi1 (Fin.ext h)
    have hi2' : i.val ≠ j.val := fun h => hi2 (Fin.ext h)
    exact simpleDiag_apply_eq_one _ (fun _ => ⟨by omega, by omega⟩)
      (fun _ _ => ⟨by omega, by omega⟩)
  · simp
  · simp

theorem prod_simpleDiag_pen (u : Fin r → kˣ) (p q s : Fin r) (hp : p.val + 1 = q.val)
    (hq : q.val + 1 = s.val) (hs : s.val + 1 = r) :
    (∏ i, simpleDiag i (u i)) q = (u p)⁻¹ * u q * u s := by
  have hpq : p ≠ q := fun h => by rw [h] at hp; omega
  have hsq : s ≠ q := fun h => by rw [h] at hq; omega
  have hsp : s ≠ p := fun h => by rw [h] at hq; omega
  rw [Finset.prod_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ s),
    Finset.prod_eq_mul p q hpq]
  · rw [simpleDiag_apply_succ hp, simpleDiag_apply_self_of_lt (by omega),
      simpleDiag_apply_last hs (by omega) (Or.inl hq)]
  · intro i hi ⟨hi1, hi2⟩
    have hi3 : i ≠ s := Finset.ne_of_mem_erase hi
    have hi1' : i.val ≠ p.val := fun h => hi1 (Fin.ext h)
    have hi2' : i.val ≠ q.val := fun h => hi2 (Fin.ext h)
    have hi3' : i.val ≠ s.val := fun h => hi3 (Fin.ext h)
    exact simpleDiag_apply_eq_one _ (fun _ => ⟨by omega, by omega⟩)
      (fun _ _ => ⟨by omega, by omega⟩)
  · intro h
    exact absurd (Finset.mem_erase.2 ⟨hsp.symm, Finset.mem_univ _⟩) h
  · intro h
    exact absurd (Finset.mem_erase.2 ⟨hsq.symm, Finset.mem_univ _⟩) h

theorem prod_simpleDiag_last (u : Fin r → kˣ) (q s : Fin r) (hq : q.val + 1 = s.val)
    (hs : s.val + 1 = r) :
    (∏ i, simpleDiag i (u i)) s = (u q)⁻¹ * u s := by
  have hqs : q ≠ s := fun h => by rw [h] at hq; omega
  rw [Finset.prod_apply, Finset.prod_eq_mul q s hqs]
  · rw [simpleDiag_apply_succ hq, simpleDiag_apply_last hs (by omega) (Or.inr rfl)]
  · intro i _ ⟨hi1, hi2⟩
    have hi1' : i.val ≠ q.val := fun h => hi1 (Fin.ext h)
    have hi2' : i.val ≠ s.val := fun h => hi2 (Fin.ext h)
    exact simpleDiag_apply_eq_one _ (fun _ => ⟨by omega, by omega⟩)
      (fun _ _ => ⟨by omega, by omega⟩)
  · simp
  · simp

theorem prod_mulSingle_mul_mulSingle (i j : Fin r) (a b : kˣ) :
    ∏ x, (Pi.mulSingle i a * Pi.mulSingle j b : Fin r → kˣ) x = a * b := by
  simp only [Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.mem_univ,
    ite_true]

end Diag

variable {E : Type*} [Group E] {π : E →* orthElementaryGroup (quadPlus r k)}

section Image

variable [Finite k] [Finite E] (hS : LiftHyp π)
include hS

theorem coe_pi_hSimple (i : Fin r) (c : kˣ) :
    ((π (hSimple π i c) : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] _) = torusElt r k (simpleDiag i c) := by
  by_cases h : i.val + 1 < r
  · rw [hSimple_of_lt h, coe_pi_hMinus hS, simpleDiag, dite_eq_left h]
  · by_cases h' : 1 ≤ i.val
    · rw [hSimple_of_not_lt h h', coe_pi_hPlus hS, simpleDiag, dite_eq_right h, dite_eq_left h']
    · rw [hSimple, simpleLift, dite_eq_right h, dite_eq_right h', MonoidHom.one_apply, map_one,
        simpleDiag, dite_eq_right h, dite_eq_right h', map_one, Subgroup.coe_one]

theorem coe_pi_thetaHom (u : Fin r → kˣ) :
    ((π (thetaHom hS u) : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] _) = torusElt r k (∏ i, simpleDiag i (u i)) := by
  change ((orthElementaryGroup (quadPlus r k)).subtype.comp π) (thetaHom hS u) = _
  rw [thetaHom_apply, map_list_prod, List.map_ofFn, ← List.prod_ofFn, map_list_prod,
    List.map_ofFn]
  congr 2
  funext i
  exact coe_pi_hSimple hS i (u i)

end Image

variable (r k) in
@[expose] noncomputable def sqTorus :
    Subgroup ((Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) where
  carrier := {g | ∃ a : Fin r → kˣ, torusElt r k a = g ∧ IsSquare (∏ i, a i)}
  mul_mem' := by
    rintro _ _ ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩
    refine ⟨a * b, map_mul _ _ _, ?_⟩
    simp only [Pi.mul_apply, Finset.prod_mul_distrib]
    exact ha.mul hb
  one_mem' := ⟨1, map_one _, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, rfl, ha⟩
    refine ⟨a⁻¹, map_inv _ _, ?_⟩
    simp only [Pi.inv_apply, Finset.prod_inv_distrib]
    exact ha.inv


section Image

variable [Finite k] [Finite E] (hS : LiftHyp π)
include hS

theorem range_pi_thetaHom (hr : 2 ≤ r) :
    ((orthElementaryGroup (quadPlus r k)).subtype.comp (π.comp (thetaHom hS))).range =
      sqTorus r k := by
  set f := (orthElementaryGroup (quadPlus r k)).subtype.comp π
  have hf : (orthElementaryGroup (quadPlus r k)).subtype.comp (π.comp (thetaHom hS)) =
      f.comp (thetaHom hS) := rfl
  have hfm : ∀ {i j : Fin r} (hij : i ≠ j) (a : kˣ),
      f (hMinus π i j hij a) = torusElt r k (Pi.mulSingle i a * Pi.mulSingle j a⁻¹) :=
    fun hij a => coe_pi_hMinus hS hij a
  have hfp : ∀ {i j : Fin r} (hij : i ≠ j) (a : kˣ),
      f (hPlus π i j hij a) = torusElt r k (Pi.mulSingle i a * Pi.mulSingle j a) :=
    fun hij a => coe_pi_hPlus hS hij a
  rw [hf, MonoidHom.range_comp, range_thetaHom hS hr]
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, liftTorus, Subgroup.closure_le]
    rintro _ (⟨i, j, hij, a, rfl⟩ | ⟨i, j, hij, a, rfl⟩)
    · refine ⟨_, (hfm hij a).symm, ?_⟩
      rw [prod_mulSingle_mul_mulSingle, mul_inv_cancel]
      exact ⟨1, (one_mul 1).symm⟩
    · exact ⟨_, (hfp hij a).symm, by rw [prod_mulSingle_mul_mulSingle]; exact ⟨a, rfl⟩⟩
  · rintro _ ⟨a, rfl, b, hb⟩
    set L : Fin r := ⟨r - 1, by omega⟩
    set L' : Fin r := ⟨r - 2, by omega⟩
    have hL'L : L' ≠ L := Fin.ne_of_val_ne (by simp [L, L']; omega)
    have hdecomp : a = (∏ j, ((Pi.mulSingle j (a j) : Fin r → kˣ) *
        (Pi.mulSingle L (a j)⁻¹ : Fin r → kˣ))) *
        ((Pi.mulSingle L' b * Pi.mulSingle L b) *
          (Pi.mulSingle L' b⁻¹ * Pi.mulSingle L b⁻¹⁻¹)) := by
      have h1 : ((Pi.mulSingle L' b * Pi.mulSingle L b) *
          (Pi.mulSingle L' b⁻¹ * Pi.mulSingle L b⁻¹⁻¹) : Fin r → kˣ) =
          Pi.mulSingle L (∏ j, a j) := by
        rw [hb, inv_inv, mul_mul_mul_comm, ← Pi.mulSingle_mul, ← Pi.mulSingle_mul,
          mul_inv_cancel, Pi.mulSingle_one, one_mul]
      rw [h1, Finset.prod_mul_distrib, Finset.univ_prod_mulSingle, mul_assoc]
      conv_lhs => rw [← mul_one a]
      congr 1
      funext y
      rw [Pi.one_apply, Pi.mul_apply, Finset.prod_apply]
      by_cases hy : y = L
      · subst hy
        simp [Finset.prod_inv_distrib]
      · simp [Pi.mulSingle_eq_of_ne hy]
    change a ∈ ((liftTorus π).map f).comap (torusElt r k)
    rw [hdecomp]
    refine mul_mem (Subgroup.prod_mem _ fun j _ => ?_) (mul_mem ?_ ?_)
    · by_cases hj : j = L
      · subst hj
        rw [← Pi.mulSingle_mul, mul_inv_cancel, Pi.mulSingle_one]
        exact one_mem _
      · exact ⟨_, hMinus_mem hj (a j), hfm hj (a j)⟩
    · exact ⟨_, hPlus_mem hL'L b, hfp hL'L b⟩
    · exact ⟨_, hMinus_mem hL'L b⁻¹, hfm hL'L b⁻¹⟩

end Image

section Kernel

theorem eq_of_prod_simpleDiag_eq_one (hr : 3 ≤ r) {u : Fin r → kˣ}
    (hu : ∏ i, simpleDiag i (u i) = 1) :
    u = 1 ∨ u = Pi.mulSingle ⟨r - 2, by omega⟩ (-1) * Pi.mulSingle ⟨r - 1, by omega⟩ (-1) := by
  have hlow : ∀ m : ℕ, ∀ j : Fin r, j.val = m → m + 3 ≤ r → u j = 1 := by
    intro m
    induction m with
    | zero =>
      intro j hj _
      have := congrFun hu j
      rwa [prod_simpleDiag_zero hr u j hj] at this
    | succ m ih =>
      intro j hj hm
      have hp := ih ⟨m, by omega⟩ rfl (by omega)
      have := congrFun hu j
      rw [prod_simpleDiag_mid u j ⟨m, by omega⟩ (by simp; omega) (by omega), hp, inv_one,
        one_mul] at this
      exact this
  set p : Fin r := ⟨r - 3, by omega⟩
  set q : Fin r := ⟨r - 2, by omega⟩
  set s : Fin r := ⟨r - 1, by omega⟩
  have hp1 : u p = 1 := hlow (r - 3) p rfl (by omega)
  have hpen := congrFun hu q
  rw [prod_simpleDiag_pen u p q s (by simp [p, q]; omega) (by simp [q, s]; omega)
    (by simp [s]; omega), hp1, inv_one, one_mul] at hpen
  have hlast := congrFun hu s
  rw [prod_simpleDiag_last u q s (by simp [q, s]; omega) (by simp [s]; omega)] at hlast
  have hsq : u s = u q := by
    have h := hlast
    rw [Pi.one_apply, inv_mul_eq_one] at h
    exact h.symm
  have hqq : (u q : k) * u q = 1 := by
    have := congrArg Units.val hpen
    rwa [Pi.one_apply, Units.val_mul, hsq, Units.val_one] at this
  have hrest : ∀ j : Fin r, j ≠ q → j ≠ s → u j = 1 := fun j hjq hjs =>
    hlow j.val j rfl (by
      have h1 : j.val ≠ r - 2 := fun h => hjq (Fin.ext h)
      have h2 : j.val ≠ r - 1 := fun h => hjs (Fin.ext h)
      omega)
  have hqs : q ≠ s := Fin.ne_of_val_ne (by simp [q, s]; omega)
  rcases mul_self_eq_one_iff.1 hqq with h | h
  · left
    funext j
    by_cases hjq : j = q
    · subst hjq
      exact Units.ext h
    by_cases hjs : j = s
    · subst hjs
      rw [hsq]
      exact Units.ext h
    exact hrest j hjq hjs
  · right
    funext j
    by_cases hjq : j = q
    · subst hjq
      rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hqs, mul_one]
      exact Units.ext (by simpa using h)
    by_cases hjs : j = s
    · subst hjs
      rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hqs.symm, Pi.mulSingle_eq_same, one_mul, hsq]
      exact Units.ext (by simpa using h)
    rw [hrest j hjq hjs, Pi.mul_apply, Pi.mulSingle_eq_of_ne hjq, Pi.mulSingle_eq_of_ne hjs,
      mul_one]

variable [Finite k] [Finite E] (hS : LiftHyp π)
include hS

theorem thetaHom_epsilon (hr : 3 ≤ r) :
    thetaHom hS (Pi.mulSingle ⟨r - 2, by omega⟩ (-1) * Pi.mulSingle ⟨r - 1, by omega⟩ (-1)) =
      hSimple π ⟨r - 2, by omega⟩ (-1) * hSimple π ⟨r - 1, by omega⟩ (-1) := by
  rw [map_mul, thetaHom_mulSingle, thetaHom_mulSingle]

theorem epsilon_sq (hr : 3 ≤ r) :
    (hSimple π ⟨r - 2, by omega⟩ (-1) * hSimple π ⟨r - 1, by omega⟩ (-1)) ^ 2 = 1 := by
  rw [← thetaHom_epsilon hS hr, ← map_pow]
  convert map_one (thetaHom hS)
  funext j
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.one_apply]
  by_cases h1 : j = ⟨r - 2, by omega⟩ <;> by_cases h2 : j = ⟨r - 1, by omega⟩ <;>
    simp [h1, h2, Pi.mulSingle_apply]

theorem epsilon_mem_ker (hr : 3 ≤ r) :
    hSimple π ⟨r - 2, by omega⟩ (-1) * hSimple π ⟨r - 1, by omega⟩ (-1) ∈ π.ker := by
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  rw [map_mul, Subgroup.coe_mul, coe_pi_hSimple hS, coe_pi_hSimple hS, ← map_mul,
    Subgroup.coe_one]
  convert map_one (torusElt r k)
  funext j
  rw [Pi.mul_apply, simpleDiag_apply, simpleDiag_apply, Pi.one_apply]
  dsimp only
  split_ifs <;> first | omega | simp

theorem liftTorus_inf_ker (hr : 3 ≤ r) :
    liftTorus π ⊓ π.ker =
      Subgroup.zpowers (hSimple π ⟨r - 2, by omega⟩ (-1) * hSimple π ⟨r - 1, by omega⟩ (-1)) := by
  apply le_antisymm
  · rintro x ⟨hxH, hxK⟩
    rw [← range_thetaHom hS (by omega)] at hxH
    obtain ⟨u, rfl⟩ := hxH
    have h1 : torusElt r k (∏ i, simpleDiag i (u i)) = torusElt r k 1 := by
      rw [← coe_pi_thetaHom hS, (MonoidHom.mem_ker).1 hxK, map_one, Subgroup.coe_one]
    rcases eq_of_prod_simpleDiag_eq_one hr (torusElt_injective h1) with rfl | rfl
    · rw [map_one]
      exact one_mem _
    · rw [thetaHom_epsilon hS hr]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact ⟨mul_mem (hSimple_mem _ _) (hSimple_mem _ _), epsilon_mem_ker hS hr⟩


end Kernel


end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
