module

public import CFSG.Monster.B.CTIB.HInnerReps
public import CFSG.Monster.B.CTIB.Rank2158Final
public import CFSG.Monster.B.CTIB.UniqueComponentAmbient

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)


theorem rank_qS_one :
    ((βr (qS 1)) - 1).rank = 1860 := by
  rw [← rs1_eq]
  exact rank_four.1

theorem rank_xs :
    ((βr xs) - 1).rank = 2048 := by
  rw [← rs0_eq]
  exact rank_four.2.1

theorem isConj_map_sEquiv_iff {a b : Sbp} : IsConj (sEquiv a) (sEquiv b) ↔ IsConj a b := by
  constructor
  · intro h
    have h' := sEquiv.symm.toMonoidHom.map_isConj h
    simpa using h'
  · exact sEquiv.toMonoidHom.map_isConj

theorem clabelS_cv0 :
    clabelS cv0 = cS := Subtype.ext clabel_cv0


theorem rank_of_adj
    {s : Sbp} {v u : CVert} (hvu : cgraph.Adj v u)
    (h : sEquiv s = clabelS v * clabelS u) : ((βr s) - 1).rank = 2048 := by
  have h1 := isConj_clabelS_mul_of_adj hvu
  rw [← h, ← sEquiv_xs, isConj_map_sEquiv_iff] at h1
  rw [rank_beta_conj h1, rank_xs]

theorem isConj_rs5_of_dist_three
    {v u : CVert} (h : cgraph.dist v u = 3) :
    IsConj (sEquiv (rs 5)) (clabelS v * clabelS u) := by
  obtain ⟨⟨v₀, u₀, h₀, hc⟩, -⟩ := native_rank_2158_distance_three_product_final
  obtain ⟨s, hs⟩ := cvMul_transitive v₀ v
  have hu₁ : cvMul u₀ s ∈ sphereDistThree v := by
    rw [mem_sphereDistThree, ← hs, dist_cvMul, h₀]
  obtain ⟨g, hgv, hgu⟩ := (distThreePaths_of_ambient ambientRootOrbitsHyp).1 v (cvMul u₀ s) u
    hu₁ (mem_sphereDistThree.2 h)
  refine hc.trans (isConj_iff.2 ⟨(s * g)⁻¹, ?_⟩)
  have ev : clabelS v = (s * g)⁻¹ * clabelS v₀ * (s * g) := by
    rw [← clabelS_cvMul, cvMul_mul, hs, hgv]
  have eu : clabelS u = (s * g)⁻¹ * clabelS u₀ * (s * g) := by
    rw [← clabelS_cvMul, cvMul_mul, hgu]
  rw [ev, eu, inv_inv]
  group

theorem rank_of_dist_three
    {s : Sbp} {v u : CVert} (hvu : cgraph.dist v u = 3)
    (h : sEquiv s = clabelS v * clabelS u) : ((βr s) - 1).rank = 2158 := by
  have h1 := isConj_rs5_of_dist_three hvu
  rw [← h, isConj_map_sEquiv_iff] at h1
  rw [← rank_beta_conj h1]
  exact rank_four.2.2.1

theorem isConj_qS_one_labelS :
    IsConj (qS 1) labelS :=
  (isConj_of_mem_jClass labelS_mem_jClass).symm


section Local

variable {v : CVert} (hv : clabelS v = sEquiv (qS 1))

include hv

theorem commute_sEquiv_iff {s : Sbp} :
    s * qS 1 = qS 1 * s ↔ ((sEquiv s : Shat) : Dfull) * clabel v = clabel v * sEquiv s := by
  rw [← coe_clabelS, hv, commute_iff_sEquiv]

theorem sEquiv_mem_vStab
    {s : Sbp} (hs : s * qS 1 = qS 1 * s) : sEquiv s ∈ vStab v :=
  ((centralizerInput_of_ambient ambientRootOrbitsHyp) v (sEquiv s)).1
    ((commute_sEquiv_iff hv).1 hs)

theorem commute_of_mem_vStab
    {y : Shat} (hy : y ∈ vStab v) :
    sEquiv.symm y * qS 1 = qS 1 * sEquiv.symm y := by
  rw [commute_sEquiv_iff hv, MulEquiv.apply_symm_apply]
  exact ((centralizerInput_of_ambient ambientRootOrbitsHyp) v y).2 hy


end Local


end CFSG.Monster.B.CTIB
