module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.Data.Fintype.Perm

public noncomputable section

namespace CFSG

open scoped Classical IsKleinFour

universe u

variable (E : Type u) [Group E]

@[expose] def nonidentityAutomorphismAction :
    MulAut E →* Equiv.Perm {x : E // x ≠ 1} where
  toFun a := Equiv.Perm.subtypePerm a.toEquiv (by
    intro x
    constructor
    · intro h hx
      exact h (hx ▸ map_one a)
    · intro hx hax
      apply hx
      apply a.injective
      simpa using hax)
  map_one' := by
    ext x
    rfl
  map_mul' a b := by
    ext x
    rfl

@[simp] theorem nonidentityAutomorphismAction_coe (a : MulAut E) (x : E) (hx : x ≠ 1) :
    (nonidentityAutomorphismAction E a ⟨x, hx⟩ : E) = a x := rfl

theorem nonidentityAutomorphismAction_injective :
    Function.Injective (nonidentityAutomorphismAction E) := by
  intro a b hab
  ext x
  by_cases hx : x = 1
  · simp [hx]
  · exact congrArg Subtype.val
      (congrArg (fun p : Equiv.Perm {x : E // x ≠ 1} => p ⟨x, hx⟩) hab)

variable [IsKleinFour E]

@[expose] def kleinFourAutomorphismOfPermutation
    (p : Equiv.Perm {x : E // x ≠ 1}) : MulAut E :=
  IsKleinFour.mulEquiv (Equiv.Perm.ofSubtype p)
    (Equiv.Perm.ofSubtype_apply_of_not_mem p (by simp))

@[simp] theorem kleinFourAutomorphismOfPermutation_coe
    (p : Equiv.Perm {x : E // x ≠ 1}) (x : E) (hx : x ≠ 1) :
    kleinFourAutomorphismOfPermutation E p x = (p ⟨x, hx⟩ : E) :=
  Equiv.Perm.ofSubtype_apply_of_mem p hx

@[simp] theorem nonidentityAutomorphismAction_ofPermutation
    (p : Equiv.Perm {x : E // x ≠ 1}) :
    nonidentityAutomorphismAction E (kleinFourAutomorphismOfPermutation E p) = p := by
  ext x
  exact kleinFourAutomorphismOfPermutation_coe E p x.val x.property

theorem nonidentityAutomorphismAction_surjective :
    Function.Surjective (nonidentityAutomorphismAction E) := by
  intro p
  exact ⟨kleinFourAutomorphismOfPermutation E p,
    nonidentityAutomorphismAction_ofPermutation E p⟩

@[expose] def kleinFourAutomorphismEquiv :
    MulAut E ≃* Equiv.Perm {x : E // x ≠ 1} :=
  MulEquiv.ofBijective (nonidentityAutomorphismAction E)
    ⟨nonidentityAutomorphismAction_injective E, nonidentityAutomorphismAction_surjective E⟩

@[simp] theorem kleinFourAutomorphismEquiv_coe (a : MulAut E) (x : E) (hx : x ≠ 1) :
    (kleinFourAutomorphismEquiv E a ⟨x, hx⟩ : E) = a x := rfl

@[simp] theorem kleinFourAutomorphismEquiv_symm_coe
    (p : Equiv.Perm {x : E // x ≠ 1}) (x : E) (hx : x ≠ 1) :
    (kleinFourAutomorphismEquiv E).symm p x = (p ⟨x, hx⟩ : E) := by
  have h := congrArg (fun q : Equiv.Perm {x : E // x ≠ 1} => (q ⟨x, hx⟩ : E))
    ((kleinFourAutomorphismEquiv E).apply_symm_apply p)
  exact h

theorem kleinFour_nonidentity_card : Nat.card {x : E // x ≠ 1} = 3 := by
  let : Fintype E := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : E => x = 1)]
  simp

theorem kleinFour_automorphism_card : Nat.card (MulAut E) = 6 := by
  let : Fintype {x : E // x ≠ 1} := Fintype.ofFinite _
  rw [Nat.card_congr (kleinFourAutomorphismEquiv E).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm,
    ← Nat.card_eq_fintype_card, kleinFour_nonidentity_card]
  decide

theorem kleinFour_automorphism_transitive (x y : E) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : MulAut E, a x = y := by
  let p : Equiv.Perm {x : E // x ≠ 1} := Equiv.swap ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨kleinFourAutomorphismOfPermutation E p, ?_⟩
  rw [kleinFourAutomorphismOfPermutation_coe E p x hx]
  exact congrArg (fun z : {x : E // x ≠ 1} => z.val)
    (Equiv.swap_apply_left ⟨x, hx⟩ ⟨y, hy⟩)

@[expose] def kleinFourAutomorphismEquivSymmetricThree :
    MulAut E ≃* Equiv.Perm (Fin 3) :=
  letI : Fintype {x : E // x ≠ 1} := Fintype.ofFinite _
  (kleinFourAutomorphismEquiv E).trans
    (Fintype.equivFinOfCardEq
      (by simpa only [Nat.card_eq_fintype_card] using kleinFour_nonidentity_card E)).permCongrHom

theorem kleinFour_automorphism_subgroup_card (H : Subgroup (MulAut E))
    (a : MulAut E) (ha : a ∈ H) (horder : orderOf a = 2) :
    Nat.card H = 2 ∨ Nat.card H = 6 := by
  have hdvd : Nat.card H ∣ 6 := by
    rw [← kleinFour_automorphism_card E]
    exact H.card_subgroup_dvd_card
  have htwo : 2 ∣ Nat.card H := by
    have h := orderOf_dvd_natCard (⟨a, ha⟩ : H)
    rw [← Subgroup.orderOf_coe, horder] at h
    exact h
  have hbound : Nat.card H ≤ 6 := Nat.le_of_dvd (by decide) hdvd
  have hcases : ∀ d : ℕ, d ≤ 6 → d ∣ 6 → 2 ∣ d → d = 2 ∨ d = 6 := by decide
  exact hcases (Nat.card H) hbound hdvd htwo

theorem kleinFour_automorphism_subgroup_eq_top_of_card_six (H : Subgroup (MulAut E))
    (hcard : Nat.card H = 6) : H = ⊤ := by
  apply H.eq_top_of_card_eq
  rw [hcard, kleinFour_automorphism_card E]

theorem kleinFour_automorphism_subgroup_alternatives (H : Subgroup (MulAut E))
    (a : MulAut E) (ha : a ∈ H) (horder : orderOf a = 2) :
    Nat.card H = 2 ∨ Nonempty (H ≃* Equiv.Perm (Fin 3)) := by
  rcases kleinFour_automorphism_subgroup_card E H a ha horder with htwo | hsix
  · exact Or.inl htwo
  · apply Or.inr
    have htop := kleinFour_automorphism_subgroup_eq_top_of_card_six E H hsix
    exact ⟨((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans
      (kleinFourAutomorphismEquivSymmetricThree E)⟩

theorem kleinFour_automorphism_subgroup_transitive (H : Subgroup (MulAut E))
    (hcard : Nat.card H = 6) (x y : E) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : H, a.val x = y := by
  obtain ⟨a, ha⟩ := kleinFour_automorphism_transitive E x y hx hy
  have htop := kleinFour_automorphism_subgroup_eq_top_of_card_six E H hcard
  exact ⟨⟨a, htop ▸ Subgroup.mem_top a⟩, ha⟩

theorem kleinFour_order_three_cycle (a : MulAut E) (horder : orderOf a = 3)
    (x : E) (hx : x ≠ 1) :
    a x ≠ x ∧ a (a x) ≠ x ∧ a (a x) ≠ a x ∧
      ∀ y : E, y ≠ 1 → y = x ∨ y = a x ∨ y = a (a x) := by
  let X := {x : E // x ≠ 1}
  let : Fintype X := Fintype.ofFinite _
  let e : X ≃ Fin 3 := Fintype.equivFinOfCardEq
    (by simpa only [X, Nat.card_eq_fintype_card] using kleinFour_nonidentity_card E)
  let f : MulAut E ≃* Equiv.Perm (Fin 3) := (kleinFourAutomorphismEquiv E).trans e.permCongrHom
  let p := f a
  have hporder : orderOf p = 3 := (f.orderOf_eq a).trans horder
  have hpow : p ^ 3 = 1 := by
    have h := pow_orderOf_eq_one p
    rw [hporder] at h
    exact h
  have hpne : p ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hporder
    exact (by decide : (1 : ℕ) ≠ 3) hporder
  have hfinite : ∀ p : Equiv.Perm (Fin 3), p ^ 3 = 1 → p ≠ 1 →
      ∀ z : Fin 3, p z ≠ z ∧ p (p z) ≠ z ∧ p (p z) ≠ p z ∧
        ∀ w : Fin 3, w = z ∨ w = p z ∨ w = p (p z) := by decide
  let ax : X := kleinFourAutomorphismEquiv E a ⟨x, hx⟩
  let aax : X := kleinFourAutomorphismEquiv E a ax
  have hpx : p (e ⟨x, hx⟩) = e ax := by
    change e (kleinFourAutomorphismEquiv E a (e.symm (e ⟨x, hx⟩))) = e ax
    rw [e.symm_apply_apply]
  have hppx : p (p (e ⟨x, hx⟩)) = e aax := by
    rw [hpx]
    change e (kleinFourAutomorphismEquiv E a (e.symm (e ax))) = e aax
    rw [e.symm_apply_apply]
  obtain ⟨hax, haax, haaxax, hcover⟩ := hfinite p hpow hpne (e ⟨x, hx⟩)
  rw [hpx] at hax
  rw [hppx] at haax
  rw [hppx, hpx] at haaxax
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro heq
    exact hax (congrArg e (Subtype.ext heq))
  · intro heq
    exact haax (congrArg e (Subtype.ext heq))
  · intro heq
    exact haaxax (congrArg e (Subtype.ext heq))
  · intro y hy
    rcases hcover (e ⟨y, hy⟩) with h | h | h
    · exact Or.inl (congrArg Subtype.val (e.injective h))
    · rw [hpx] at h
      exact Or.inr (Or.inl (congrArg Subtype.val (e.injective h)))
    · rw [hppx] at h
      exact Or.inr (Or.inr (congrArg Subtype.val (e.injective h)))


section NormalizerCapture


end NormalizerCapture

end CFSG
