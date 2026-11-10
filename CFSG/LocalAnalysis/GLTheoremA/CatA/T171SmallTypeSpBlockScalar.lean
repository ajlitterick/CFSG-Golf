module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.ClassicalGroups.Alternating
open CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine
open LinearMap (BilinForm)
open Matrix CFSG.LieType.SteinbergBR.EvenSp

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]


private theorem GL2_zmod2_centralizer_disj (y M : GL (Fin 2) (ZMod 2))
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hM : M * y = y * M) :
    M = 1 ∨ M = y ∨ M = y ^ 2 := by
  have h : ∀ y : GL (Fin 2) (ZMod 2), y ^ 3 = 1 → y ≠ 1 →
      ∀ M : GL (Fin 2) (ZMod 2), M * y = y * M →
      M = 1 ∨ M = y ∨ M = y ^ 2 := by decide
  exact h y hy3 hy1 M hM

theorem GL2_zmod2_centralizer_mem_zpowers (y M : GL (Fin 2) (ZMod 2))
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hM : M * y = y * M) :
    M ∈ Subgroup.zpowers y := by
  rcases GL2_zmod2_centralizer_disj y M hy3 hy1 hM with rfl | rfl | rfl
  · rw [Subgroup.mem_zpowers_iff]
    exact ⟨0, by simp⟩
  · exact Subgroup.mem_zpowers _
  · rw [Subgroup.mem_zpowers_iff]
    exact ⟨2, by simp⟩


noncomputable def linearEquivMulEquivGL {P : Type*} [AddCommGroup P] [Module (ZMod 2) P]
    [FiniteDimensional (ZMod 2) P] (hP : Module.finrank (ZMod 2) P = 2) :
    (P ≃ₗ[ZMod 2] P) ≃* GL (Fin 2) (ZMod 2) :=
  let b : Module.Basis (Fin 2) (ZMod 2) P := Module.finBasisOfFinrankEq (ZMod 2) P hP
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) P).symm.trans
    (Matrix.GeneralLinearGroup.toLin' b).symm

theorem linearEquiv_centralizer_zpowers {P : Type*} [AddCommGroup P] [Module (ZMod 2) P]
    [FiniteDimensional (ZMod 2) P] (hP : Module.finrank (ZMod 2) P = 2)
    {y g : P ≃ₗ[ZMod 2] P} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hg : g * y = y * g) :
    g ∈ Subgroup.zpowers y := by
  let σ := linearEquivMulEquivGL hP
  have hy3' : σ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hy1' : σ y ≠ 1 := by
    intro h
    exact hy1 (σ.injective (by rw [h, map_one]))
  have hg' : σ g * σ y = σ y * σ g := by rw [← map_mul, ← map_mul, hg]
  have hmem := GL2_zmod2_centralizer_mem_zpowers (σ y) (σ g) hy3' hy1' hg'
  rw [Subgroup.mem_zpowers_iff] at hmem ⊢
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  apply σ.injective
  rw [map_zpow, hk]

theorem linearEquiv_centralizer_zpowers_nat {P : Type*} [AddCommGroup P] [Module (ZMod 2) P]
    [FiniteDimensional (ZMod 2) P] (hP : Module.finrank (ZMod 2) P = 2)
    {y g : P ≃ₗ[ZMod 2] P} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hg : g * y = y * g) :
    ∃ k : ℕ, k < 3 ∧ y ^ k = g := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfin : IsOfFinOrder y := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hy3⟩
  have hmem : g ∈ Subgroup.zpowers y := linearEquiv_centralizer_zpowers hP hy3 hy1 hg
  rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hfin, orderOf_eq_prime hy3 hy1] at hmem
  obtain ⟨k, hk, hkg⟩ := Finset.mem_image.mp hmem
  exact ⟨k, Finset.mem_range.mp hk, hkg⟩

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
