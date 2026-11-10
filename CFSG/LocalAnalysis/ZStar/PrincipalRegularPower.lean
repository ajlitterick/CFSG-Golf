module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import CFSG.LocalAnalysis.ZStar.BrauerCoefficientFormula
public import Mathlib.GroupTheory.Nilpotent

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG

namespace ZStar.PrincipalRegularPower

open ZStar.Helpers ZStar
  ZStar.BrauerProjection ZStar.BrauerPrincipal
  ZStar.BrauerBlockLift ZStar.BrauerCoefficientFormula

universe u

noncomputable section

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

@[expose] noncomputable def twoRegularSum (X : Type*) [Group X] [Fintype X] :
    GroupAlgebraTwo X := by
  classical
  exact ∑ x : X, if Odd (orderOf x) then MonoidAlgebra.single x 1 else 0

@[simp]
theorem twoRegularSum_coeff (X : Type*) [Group X] [Fintype X] (x : X) :
    (twoRegularSum X).coeff x = if Odd (orderOf x) then 1 else 0 := by
  classical
  unfold twoRegularSum
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply']
  calc
    (∑ k : X,
        (if Odd (orderOf k) then
          MonoidAlgebra.single k (1 : ZMod 2) else 0).coeff x) =
        (if Odd (orderOf x) then
          MonoidAlgebra.single x (1 : ZMod 2) else 0).coeff x := by
      apply Finset.sum_eq_single
      · intro b _ hbx
        by_cases hb : Odd (orderOf b) <;> simp [hb, hbx]
      · simp
    _ = if Odd (orderOf x) then 1 else 0 := by
      by_cases hx : Odd (orderOf x) <;> simp [hx]

theorem twoRegularSum_central (X : Type*) [Group X] [Fintype X] :
    IsGroupCentral X (twoRegularSum X) := by
  intro g
  ext x
  simp only [MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one,
    twoRegularSum_coeff]
  have hconj : g * (g⁻¹ * x) * g⁻¹ = x * g⁻¹ := by group
  have hiff : Odd (orderOf (g⁻¹ * x)) ↔ Odd (orderOf (x * g⁻¹)) := by
    rw [← hconj, orderOf_conj_eq]
  by_cases h : Odd (orderOf (g⁻¹ * x))
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun hx => h (hiff.mpr hx))]

theorem augmentation_twoRegularSum (X : Type*) [Group X] [Fintype X] :
    augmentationHom X (twoRegularSum X) = 1 := by
  classical
  let s : Finset X :=
    (Finset.univ.filter fun x : X => Odd (orderOf x)).erase 1
  have hs : (∑ x ∈ s, (1 : ZMod 2)) = 0 := by
    apply Finset.sum_involution (fun x _ => x⁻¹)
    · intro x hx
      exact CharTwo.add_self_eq_zero 1
    · intro x hx _ hfix
      have hxne : x ≠ 1 := by
        exact (Finset.mem_erase.mp hx).1
      have hx2 : x * x = 1 := by
        have h := congrArg (fun y : X => x * y) hfix.symm
        simpa only [mul_inv_cancel] using h
      have hord : orderOf x = 2 :=
        orderOf_eq_prime (by simpa [pow_two] using hx2) hxne
      have hodd : Odd (orderOf x) :=
        (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2
      rw [hord] at hodd
      obtain ⟨k, hk⟩ := hodd
      omega
    · intro x hx
      exact inv_inv x
    · intro x hx
      rw [Finset.mem_erase] at hx ⊢
      refine ⟨?_, ?_⟩
      · intro h
        apply hx.1
        exact inv_eq_one.mp h
      · rw [Finset.mem_filter] at hx ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa using hx.2.2
  rw [augmentationHom_apply]
  unfold augmentationTwo
  simp only [twoRegularSum_coeff]
  have hone : Odd (orderOf (1 : X)) := by simp
  calc
    (∑ x : X, if Odd (orderOf x) then (1 : ZMod 2) else 0) =
        ∑ x ∈ (Finset.univ.filter fun x : X => Odd (orderOf x)),
          (1 : ZMod 2) := by
      rw [Finset.sum_filter]
    _ = 1 + ∑ x ∈ s, (1 : ZMod 2) := by
      rw [show (Finset.univ.filter fun x : X => Odd (orderOf x)) =
          insert 1 s by
        ext x
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_erase]
        constructor
        · intro hx
          by_cases h : x = 1
          · exact Or.inl h
          · exact Or.inr ⟨h, by simpa using hx⟩
        · rintro (rfl | ⟨_, hx⟩)
          · exact hone
          · exact hx]
      rw [Finset.sum_insert]
      simp [s]
    _ = 1 := by rw [hs, add_zero]


theorem brauerProjection_twoRegularSum (w : G) :
    brauerProjection w (twoRegularSum G) =
      twoRegularSum (involutionCentralizer w) := by
  ext x
  rw [brauerProjection_coeff, twoRegularSum_coeff, twoRegularSum_coeff]
  have horder : orderOf (x : G) = orderOf x := Subgroup.orderOf_coe x
  by_cases h : Odd (orderOf (x : G))
  · rw [ite_eq_left h, ite_eq_left (horder ▸ h)]
  · rw [ite_eq_right h, ite_eq_right (fun hx => h (horder.symm ▸ hx))]


end

end ZStar.PrincipalRegularPower

end CFSG
