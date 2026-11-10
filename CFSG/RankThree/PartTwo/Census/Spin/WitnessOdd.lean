module

public import CFSG.RankThree.PartTwo.Census.Spin.Witness

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti
open scoped commutatorElement

theorem odd_neg_one_int : Odd (-1 : ℤ) := ⟨-1, by norm_num⟩

namespace RootData

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (R : RootData K N ι)

theorem eq_zero_of_commute_x_y {i : ι} {u : K} (h : Commute (R.x i u) (R.y i 1)) : u = 0 := by
  have hm := congrArg R.mat h.eq
  rw [mat_mul, mat_mul, mat_x, mat_y, SqZeroPair.φ_upper, SqZeroPair.φ_lower, one_smul] at hm
  have e : (1 + u • R.E i) * (1 + R.F i) - (1 + R.F i) * (1 + u • R.E i) =
      u • (R.E i * R.F i - R.F i * R.E i) := by
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    module
  rw [hm, sub_self] at e
  rcases smul_eq_zero.mp e.symm with hu | hEF
  · exact hu
  · exfalso
    apply R.E_ne_zero i
    have h1 := (R.sqZero i).efe
    rw [sub_eq_zero.mp hEF, mul_assoc, (R.sqZero i).ee, mul_zero] at h1
    exact h1.symm

section Frobenius

variable {σ : K →+* K} {F : R.G →* R.G}

@[expose] def RootsInCommutator (σ : K →+* K) (F : R.G →* R.G) : Prop :=
  ∀ i u, u ∈ fixedField σ → R.x i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ ∧
    R.y i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆

theorem rootsInCommutator_of_unit (hF : R.IsFrobenius σ F) (hdiag : ∀ j, R.CM j j = 2)
    {μ : Kˣ} (hμ : (μ : K) ∈ fixedField σ) (hμ2 : (μ : K) ^ 2 ≠ 1) :
    R.RootsInCommutator σ F :=
  fun _ _ hu => ⟨x_mem_commutator hF hdiag hμ hμ2 hu, y_mem_commutator hF hdiag hμ hμ2 hu⟩

theorem rootsInCommutator_of_odd (hF : R.IsFrobenius σ F) (h2 : (2 : K) ≠ 0)
    (hodd : ∀ i, ∃ j, Odd (R.CM j i)) : R.RootsInCommutator σ F := by
  intro i u hu
  obtain ⟨j, hj⟩ := hodd i
  have hm : ((-1 : Kˣ) : K) ∈ fixedField σ := by
    rw [Units.val_neg, Units.val_one]
    exact (fixedField σ).neg_mem (fixedField σ).one_mem
  have h2F : (2 : K) ∈ fixedField σ := by
    have := (fixedField σ).add_mem (fixedField σ).one_mem (fixedField σ).one_mem
    rwa [one_add_one_eq_two] at this
  have hw : -u / 2 ∈ fixedField σ := (fixedField σ).div_mem ((fixedField σ).neg_mem hu) h2F
  have hpow : (-1 : Kˣ) ^ R.CM j i = -1 := hj.neg_one_zpow
  constructor
  · have hc : R.x i u = ⁅R.h j (-1), R.x i (-u / 2)⁆ := by
      rw [commutatorElement_def, h_conj_x, hpow, x_inv, ← x_add]
      congr 1
      rw [Units.val_neg, Units.val_one]
      field_simp
      ring
    rw [hc]
    exact Subgroup.commutator_mem_commutator (h_mem_fixed hF hm) (x_mem_fixed hF hw)
  · have hc : R.y i u = ⁅R.h j (-1), R.y i (-u / 2)⁆ := by
      rw [commutatorElement_def, h_conj_y, hpow, inv_neg_one, y_inv, ← y_add]
      congr 1
      rw [Units.val_neg, Units.val_one]
      field_simp
      ring
    rw [hc]
    exact Subgroup.commutator_mem_commutator (h_mem_fixed hF hm) (y_mem_fixed hF hw)

theorem h_mem_commutator_of (hR : R.RootsInCommutator σ F) {i : ι} {c : Kˣ}
    (hc : (c : K) ∈ fixedField σ) : R.h i c ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  have hc' : -((c⁻¹ : Kˣ) : K) ∈ fixedField σ := by
    rw [Units.val_inv_eq_inv_val]
    exact (fixedField σ).neg_mem ((fixedField σ).inv_mem hc)
  have hone := (fixedField σ).one_mem
  have hmone := (fixedField σ).neg_mem hone
  rw [h_eq]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hR i _ hc).1
    (hR i _ hc').2) (hR i _ hc).1) (Subgroup.inv_mem _ ?_)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hR i _ hone).1 (hR i _ hmone).2) (hR i _ hone).1

theorem torus_mem_commutator_of (hR : R.RootsInCommutator σ F) {s : ι → Kˣ}
    (hs : ∀ j, ((s j : Kˣ) : K) ∈ fixedField σ) :
    R.torus s ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ :=
  R.torus_mem_of_h_mem fun _ => h_mem_commutator_of R hR (hs _)


end Frobenius

end RootData

end CFSG.RankThree.PartTwo.Census.Spin
