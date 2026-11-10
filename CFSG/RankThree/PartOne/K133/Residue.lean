module

public import CFSG.RankThree.PartOne.K133.Lift
public import CFSG.RankThree.PartOne.K133.Count
public import CFSG.RankThree.PartOne.K133.Union
public import CFSG.RankThree.PartOne.K133.Two
public import CFSG.RankThree.PartOne.K133.ParA
public import CFSG.RankThree.PartOne.K133.ParAFix
import CFSG.RankThree.PartOne.S12.Sec125Moved
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_thetaQuotientCentralizer_of_rel {p : ℕ} {E I J : Subgroup G} {b : G} (hbE : b ∈ E)
    (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (hJb : J ≤ Subgroup.centralizer ({b} : Set G)) (hIJ : sectionTenRel p I J) :
    b ∈ thetaQuotientCentralizer p E I := by
  rw [mem_thetaQuotientCentralizer_iff]
  refine ⟨hbE, hEI hbE, fun y hy => ?_⟩
  have hy' : y ∈ ((I ⊓ J : Subgroup G) : Set G) *
      (inSubgroup (aschbacherSolvableCore p) I : Set G) := by
    rw [← sectionTenRel_iff.1 hIJ]
    exact hy
  obtain ⟨j, hj, n, hn, rfl⟩ := hy'
  have hjb : j * b = b * j :=
    Subgroup.mem_centralizer_singleton_iff.1 (hJb (Subgroup.mem_inf.1 hj).2)
  have hbj : b * j * b⁻¹ = j := by rw [← hjb]; group
  have hbn : b * n * b⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) I :=
    theta_conj_mem_of_normalizer p I (hEI hbE) hn
  have hkey : b * (j * n) * b⁻¹ * (j * n)⁻¹ = j * (b * n * b⁻¹ * n⁻¹) * j⁻¹ := by
    calc b * (j * n) * b⁻¹ * (j * n)⁻¹
        = (b * j * b⁻¹) * (b * n * b⁻¹) * n⁻¹ * j⁻¹ := by group
      _ = j * (b * n * b⁻¹) * n⁻¹ * j⁻¹ := by rw [hbj]
      _ = j * (b * n * b⁻¹ * n⁻¹) * j⁻¹ := by group
  rw [hkey]
  exact theta_conj_mem p I (Subgroup.mem_inf.1 hj).1
    ((inSubgroup (aschbacherSolvableCore p) I).mul_mem hbn
      ((inSubgroup (aschbacherSolvableCore p) I).inv_mem hn))


end CFSG.RankThree.PartOne.K133
