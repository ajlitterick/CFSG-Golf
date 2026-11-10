module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
public import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.GroupTheory.GroupAction.Quotient

public section

namespace CFSG.StandardType.GGHalfJoin

open CFSG.StandardType.SpJoin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem signed_mem_form {n p : ℕ} {g : Equiv.Perm (Fin n → Multiplicative (ZMod p))}
    (hg : g ∈ spSignedGroup n p) :
    ∃ σ : Equiv.Perm (Fin n), ∃ s : Fin n → ℤ,
      (∀ t, s t = 1 ∨ s t = -1) ∧ ∀ w t, g w t = (w (σ.symm t)) ^ (s t) := by
  classical
  let P : Equiv.Perm (Fin n → Multiplicative (ZMod p)) → Prop := fun g =>
    ∃ σ : Equiv.Perm (Fin n), ∃ s : Fin n → ℤ,
      (∀ t, s t = 1 ∨ s t = -1) ∧ ∀ w t, g w t = (w (σ.symm t)) ^ (s t)
  have hgen : ∀ x ∈ Set.range (spReflPerm n p), P x := by
    rintro x ⟨k, rfl⟩
    by_cases hk : k.val + 1 < n
    · refine ⟨Equiv.swap k ⟨k.val + 1, hk⟩, fun _ => 1, fun t => Or.inl rfl, ?_⟩
      intro w t
      rw [spReflPerm_of_lt n p k hk]
      simp
    · refine ⟨Equiv.refl (Fin n), fun t => if t = k then -1 else 1, ?_, ?_⟩
      · intro t
        by_cases h : t = k <;> simp [h]
      · intro w t
        rw [spReflPerm_of_not_lt n p k hk, coordInv_apply]
        by_cases ht : t = k
        · subst ht
          simp
        · rw [Function.update_of_ne ht]
          simp [ht]
  have hone : P 1 := by
    refine ⟨Equiv.refl (Fin n), fun _ => 1, fun t => Or.inl rfl, ?_⟩
    intro w t
    simp
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨σx, sx, hsx, hx⟩ ⟨σy, sy, hsy, hy⟩
    refine ⟨σx * σy, fun t => sy (σx.symm t) * sx t, ?_, ?_⟩
    · intro t
      change sy (σx.symm t) * sx t = 1 ∨ sy (σx.symm t) * sx t = -1
      rcases hsx t with h | h <;> rcases hsy (σx.symm t) with h' | h' <;>
        rw [h, h'] <;> norm_num
    · intro w t
      rw [Equiv.Perm.mul_apply, hx, hy]
      dsimp only
      have hsymm : (σx * σy).symm t = σy.symm (σx.symm t) := by
        change (σx * σy)⁻¹ t = σy.symm (σx.symm t)
        rw [mul_inv_rev, Equiv.Perm.mul_apply]
        simp only [Equiv.Perm.inv_def]
      rw [hsymm]
      exact (zpow_mul _ _ _).symm
  have hinv : ∀ x, P x → P x⁻¹ := by
    rintro x ⟨σ, s, hs, hx⟩
    refine ⟨σ.symm, fun t => s (σ t), fun t => hs (σ t), ?_⟩
    intro w t
    have hyform : ∀ u, x (fun v => (w (σ v)) ^ (s (σ v))) u = w u := by
      intro u
      rw [hx]
      rw [σ.apply_symm_apply]
      calc (w u ^ s u) ^ s u = w u ^ (s u * s u) := (zpow_mul _ _ _).symm
        _ = w u ^ (1 : ℤ) := by
            rw [show s u * s u = 1 by
              rcases hs u with h | h <;> rw [h] <;> norm_num]
        _ = w u := zpow_one _
    have hw_eq : w = x (fun v => (w (σ v)) ^ (s (σ v))) :=
      funext fun u => (hyform u).symm
    have hxinv : x⁻¹ w = fun v => (w (σ v)) ^ (s (σ v)) := by
      conv_lhs => rw [hw_eq]
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [hxinv]
    dsimp only
    rw [Equiv.symm_symm]
  exact Subgroup.closure_induction (p := fun g _ => P g) hgen hone
    (fun x y _ _ hx hy => hmul x y hx hy) (fun x _ hx => hinv x hx) hg

theorem signed_preserves_support {n : ℕ} {g : Equiv.Perm (Fin n → Multiplicative (ZMod 3))}
    (hg : g ∈ spSignedGroup n 3) {v : Fin n → Multiplicative (ZMod 3)} {i j : Fin n}
    (hij : i ≠ j) (hvi : v i ≠ 1) (hvj : v j ≠ 1) (hsupp : ∀ l, l ≠ i → l ≠ j → v l = 1)
    (hfix : g v = v) {w : Fin n → Multiplicative (ZMod 3)} (hw : ∀ l, l ≠ i → l ≠ j → w l = 1) :
    ∀ l, l ≠ i → l ≠ j → g w l = 1 := by
  classical
  obtain ⟨σ, s, hs, hform⟩ := signed_mem_form hg
  have hsupp' : ∀ l, v l ≠ 1 ↔ (l = i ∨ l = j) := by
    intro l
    constructor
    · intro hvl
      by_contra h
      rw [not_or] at h
      exact hvl (hsupp l h.1 h.2)
    · rintro (rfl | rfl)
      · exact hvi
      · exact hvj
  have hpow : ∀ t, v t = (v (σ.symm t)) ^ (s t) := by
    intro t
    have h := hform v t
    rwa [hfix] at h
  have hiff : ∀ l, (v l ≠ 1 ↔ v (σ.symm l) ≠ 1) := by
    intro l
    rw [hpow l]
    rcases hs l with h | h
    · rw [h, zpow_one]
    · rw [h, zpow_neg_one]
      exact inv_ne_one
  have key : ∀ l, l ≠ i → l ≠ j → σ.symm l ≠ i ∧ σ.symm l ≠ j := by
    intro l hl hlj
    constructor
    · intro h
      have hv : v (σ.symm l) ≠ 1 := by rw [h]; exact hvi
      have : v l ≠ 1 := (hiff l).mpr hv
      rcases (hsupp' l).mp this with h' | h'
      · exact hl h'
      · exact hlj h'
    · intro h
      have hv : v (σ.symm l) ≠ 1 := by rw [h]; exact hvj
      have : v l ≠ 1 := (hiff l).mpr hv
      rcases (hsupp' l).mp this with h' | h'
      · exact hl h'
      · exact hlj h'
  intro l hl hlj
  obtain ⟨hnei, hnej⟩ := key l hl hlj
  rw [hform w l, hw (σ.symm l) hnei hnej]
  exact one_zpow (s l)


theorem frame_upper {G : Type} [Group G] [Finite G] {k : ℕ} {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} (hA : GGWeylOfType 3 (CoxeterMatrix.B (k + 1)) A)
    (Φ : (Fin (k + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs)
    (hΦ : ∀ h ∈ spSignedGroup (k + 1) 3, ∃ ψ ∈ A, ∀ a, ψ (Φ a) = Φ (h a)) :
    ∀ ψ ∈ A, ∃ h ∈ spSignedGroup (k + 1) 3, ∀ a, ψ (Φ a) = Φ (h a) := by
  classical
  obtain ⟨e, _⟩ := hA
  haveI : Finite ↥Bs := Finite.of_injective (fun x : ↥Bs => (x : G)) Subtype.val_injective
  haveI : Finite ↥A := Finite.of_injective
    (fun ψ : ↥A => fun x : ↥Bs => (ψ : MulAut ↥Bs) x)
    (by
      intro ψ ψ' h
      exact Subtype.ext (DFunLike.ext _ _ (fun x => congrFun h x)))
  let S : Type := ↥(spSignedGroup (k + 1) 3)
  let ψh : S → MulAut ↥Bs := fun h => Classical.choose (hΦ h.1 h.2)
  have hψA : ∀ h : S, ψh h ∈ A := fun h => (Classical.choose_spec (hΦ h.1 h.2)).1
  have hψ : ∀ (h : S) (a : Fin (k + 1) → Multiplicative (ZMod 3)),
      ψh h (Φ a) = Φ (h.1 a) := fun h => (Classical.choose_spec (hΦ h.1 h.2)).2
  let f : S → ↥A := fun h => ⟨ψh h, hψA h⟩
  have hf : Function.Injective f := by
    intro h h' hh
    have hψeq : ψh h = ψh h' := congrArg Subtype.val hh
    have hab : ∀ a, h.1 a = h'.1 a := by
      intro a
      apply Φ.injective
      rw [← hψ h a, ← hψ h' a, hψeq]
    exact Subtype.ext (Equiv.ext hab)
  have hAle : Nat.card ↥A ≤ Nat.card S := by
    have hcard : Nat.card ↥A = Nat.card (CoxeterMatrix.B (k + 1)).Group :=
      (Nat.card_congr e.toEquiv).symm
    rw [hcard]
    calc Nat.card (CoxeterMatrix.B (k + 1)).Group
        ≤ 2 ^ (k + 1) * (k + 1).factorial := card_coxeterB_le (k + 1)
      _ ≤ Nat.card S :=
          two_pow_mul_factorial_le_card_spSignedGroup Nat.prime_three (by norm_num)
  have hbij : Function.Bijective f :=
    Function.Injective.bijective_of_nat_card_le hf hAle
  intro ψ hψmem
  obtain ⟨h, hh⟩ := hbij.2 ⟨ψ, hψmem⟩
  refine ⟨h.1, h.2, ?_⟩
  have hψeq : ψh h = ψ := congrArg Subtype.val hh
  intro a
  rw [← hψeq]
  exact hψ h a


end CFSG.StandardType.GGHalfJoin

end
