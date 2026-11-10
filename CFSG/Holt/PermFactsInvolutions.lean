module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.Holt

open Equiv Equiv.Perm Finset

open scoped Nat

section Parity

variable {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

theorem cycleType_eq_replicate_of_sq_eq_one {π : Perm Ψ} (hπ : π ^ 2 = 1) :
    π.cycleType = Multiset.replicate (#π.support / 2) 2 := by
  have h := cycleType_of_pow_prime_eq_one hπ
  have hs : #π.support = Multiset.card π.cycleType * 2 := by
    rw [← sum_cycleType, h]
    simp
  rw [hs, Nat.mul_div_cancel _ two_pos]
  exact h

theorem card_support_add_card_fixedPoints (π : Perm Ψ) :
    #π.support + Fintype.card (Function.fixedPoints π) = Fintype.card Ψ := by
  rw [card_fixedPoints, sum_cycleType, Nat.add_sub_cancel' (card_le_univ _)]

theorem sign_eq_neg_one_pow_of_sq_eq_one {π : Perm Ψ} (hπ : π ^ 2 = 1) :
    sign π = (-1) ^ (#π.support / 2) := by
  rw [sign_of_pow_two_eq_one hπ, ← card_support_add_card_fixedPoints π, Nat.add_sub_cancel]

theorem sign_eq_one_iff_four_dvd_card_support {π : Perm Ψ} (hπ : π ^ 2 = 1) :
    sign π = 1 ↔ 4 ∣ #π.support := by
  obtain ⟨m, hm⟩ := two_dvd_card_support hπ
  rw [sign_eq_neg_one_pow_of_sq_eq_one hπ, hm, Nat.mul_div_cancel_left _ two_pos,
    neg_one_pow_eq_one_iff_even (by decide)]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩

theorem sign_eq_one_iff_four_dvd_card_sub {π : Perm Ψ} (hπ : π ^ 2 = 1) :
    sign π = 1 ↔ 4 ∣ Nat.card Ψ - Nat.card (Function.fixedPoints π) := by
  rw [sign_eq_one_iff_four_dvd_card_support hπ, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, ← card_support_add_card_fixedPoints π, Nat.add_sub_cancel]

theorem card_support_eq_of_existsUnique {π : Perm Ψ} (h : ∃! x, π x = x) :
    #π.support + 1 = Nat.card Ψ := by
  obtain ⟨a, ha, huniq⟩ := h
  have hfix : Fintype.card (Function.fixedPoints π) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨a, ha⟩, fun ⟨y, hy⟩ => Subtype.ext (huniq y hy)⟩
  rw [Nat.card_eq_fintype_card, ← card_support_add_card_fixedPoints π, hfix]

theorem existsUnique_of_card_support_add_one {π : Perm Ψ} (h : #π.support + 1 = Nat.card Ψ) :
    ∃! x, π x = x := by
  have hfix : Fintype.card (Function.fixedPoints π) = 1 := by
    have := card_support_add_card_fixedPoints π
    rw [Nat.card_eq_fintype_card] at h
    omega
  obtain ⟨⟨a, ha⟩, hu⟩ := Fintype.card_eq_one_iff.mp hfix
  exact ⟨a, ha, fun y hy => congrArg Subtype.val (hu ⟨y, hy⟩)⟩

theorem sign_eq_one_iff_of_existsUnique {π : Perm Ψ} (hπ : π ^ 2 = 1) (h : ∃! x, π x = x) :
    sign π = 1 ↔ Nat.card Ψ % 4 = 1 := by
  rw [sign_eq_one_iff_four_dvd_card_support hπ, ← card_support_eq_of_existsUnique h]
  omega

end Parity

section Conjugacy

variable {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

theorem exists_mem_alternatingGroup_conj_eq {π τ : Perm Ψ} (hτ : sign τ = -1)
    (hπτ : Commute π τ) (g : Perm Ψ) :
    ∃ h ∈ alternatingGroup Ψ, h * π * h⁻¹ = g * π * g⁻¹ := by
  rcases Int.units_eq_one_or (sign g) with hg | hg
  · exact ⟨g, hg, rfl⟩
  · refine ⟨g * τ, by simp [mem_alternatingGroup, hg, hτ], ?_⟩
    rw [mul_inv_rev, mul_assoc g τ π, ← hπτ.eq]
    group

omit [Fintype Ψ] in
theorem commute_swap_of_sq_eq_one {π : Perm Ψ} (hπ : π ^ 2 = 1) (a : Ψ) :
    Commute π (swap a (π a)) := by
  have h2 : π (π a) = a := by
    simpa [sq] using congrArg (fun f : Perm Ψ => f a) hπ
  rw [Commute, SemiconjBy, mul_swap_eq_swap_mul, h2, swap_comm]

theorem exists_mem_alternatingGroup_conj_eq_of_card_support_eq {π σ : Perm Ψ} (hπ : π ^ 2 = 1)
    (hσ : σ ^ 2 = 1) (h : #π.support = #σ.support) :
    ∃ g ∈ alternatingGroup Ψ, g * π * g⁻¹ = σ := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp ((isConj_iff_cycleType_eq (σ := π) (τ := σ)).mpr (by
    rw [cycleType_eq_replicate_of_sq_eq_one hπ, cycleType_eq_replicate_of_sq_eq_one hσ, h]))
  by_cases h1 : π = 1
  · exact ⟨1, one_mem _, by simp [h1]⟩
  · obtain ⟨a, ha⟩ : ∃ a, π a ≠ a := by
      by_contra! h'
      exact h1 (Equiv.ext h')
    exact exists_mem_alternatingGroup_conj_eq (sign_swap ha.symm)
      (commute_swap_of_sq_eq_one hπ a) g


end Conjugacy

section Lifting

variable {G H : Type*} [Group G] [Group H]


theorem exists_isPGroup_le_map_eq [Finite G] {p : ℕ} [Fact p.Prime] (ρ : G →* H)
    {K : Subgroup G} {R : Subgroup H} (hR : IsPGroup p R) (hRK : R ≤ K.map ρ) :
    ∃ P ≤ K, IsPGroup p P ∧ P.map ρ = R := by
  set L : Subgroup G := K ⊓ R.comap ρ
  let g : L →* R := (ρ.comp L.subtype).codRestrict R fun x => x.2.2
  have hf : Function.Surjective g := by
    rintro ⟨r, hr⟩
    obtain ⟨k, hk, rfl⟩ := hRK hr
    exact ⟨⟨k, hk, hr⟩, rfl⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p L))
  have htop : (T : Subgroup L).map g = ⊤ :=
    (T.mapSurjective hf).is_maximal' (hR.to_subgroup ⊤) le_top |>.symm
  refine ⟨(T : Subgroup L).map L.subtype, ?_, T.isPGroup'.map _, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2.1
  · rw [Subgroup.map_map]
    have : ρ.comp L.subtype = R.subtype.comp g := rfl
    rw [this, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Lifting

section Centralizer


variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]


end Centralizer

section BlockTranslation

variable {Γ ι A : Type*} [AddCommGroup A] (e : Γ ≃ ι × A)

@[expose] def blockTranslate (f : ι → A) : Perm Γ where
  toFun γ := e.symm ((e γ).1, (e γ).2 + f (e γ).1)
  invFun γ := e.symm ((e γ).1, (e γ).2 - f (e γ).1)
  left_inv γ := by simp
  right_inv γ := by simp

@[simp]
theorem apply_blockTranslate (f : ι → A) (γ : Γ) :
    e (blockTranslate e f γ) = ((e γ).1, (e γ).2 + f (e γ).1) := by
  simp [blockTranslate]


@[simp]
theorem blockTranslate_zero : blockTranslate e (0 : ι → A) = 1 := by
  ext γ
  apply e.injective
  simp


end BlockTranslation

section FourGroup

@[expose] def fourRot (v : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 := (v.2, v.1 + v.2)


theorem fourRot_fourRot_fourRot (v : ZMod 2 × ZMod 2) : fourRot (fourRot (fourRot v)) = v := by
  revert v
  unfold fourRot
  decide


variable {Γ ι : Type*} (e : Γ ≃ ι × (ZMod 2 × ZMod 2))

@[expose] def blockRotate : Perm Γ where
  toFun γ := e.symm ((e γ).1, fourRot (e γ).2)
  invFun γ := e.symm ((e γ).1, fourRot (fourRot (e γ).2))
  left_inv γ := by simp [fourRot_fourRot_fourRot]
  right_inv γ := by simp [fourRot_fourRot_fourRot]

@[simp]
theorem apply_blockRotate (γ : Γ) : e (blockRotate e γ) = ((e γ).1, fourRot (e γ).2) := by
  simp [blockRotate]


end FourGroup

section FixedPointFree


end FixedPointFree

end CFSG.Holt
