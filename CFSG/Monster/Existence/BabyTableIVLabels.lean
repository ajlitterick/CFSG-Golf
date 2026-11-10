module

public import CFSG.Monster.B.CTIB.DistThreeProductCore
public import CFSG.Monster.B.CTIB.Rank2158Final
public import CFSG.Monster.GMS.Facts.BabyTables
public import CFSG.Monster.GMS.Facts.TableV

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.GMS

@[expose] def labelSphere
    (k : Fin 4) (v : CVert) : Set CVert :=
  match k with
  | 0 => cgraph.neighborSet v
  | 1 => sphereDistThree v
  | 2 => sphereThree v
  | 3 => sphereFour v

theorem clabelS_injective :
    Function.Injective clabelS := fun _ _ h =>
  (global_label_of_ambient ambientRootOrbitsHyp).1 (congrArg Subtype.val h)

theorem labelSphere_cover
    (v u : CVert) : u = v ∨ ∃ k, u ∈ labelSphere k v := by
  obtain ⟨-, -, -, hv, -⟩ := diameter_three_rank_five_of_ambient ambientRootOrbitsHyp
  rcases (hv v).1 u with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨0, h⟩
  · exact Or.inr ⟨2, h⟩
  · exact Or.inr ⟨3, h⟩
  · exact Or.inr ⟨1, h⟩

theorem labelSphere_ncard
    (k : Fin 4) (v : CVert) : (labelSphere k v).ncard = babyOrbitSize k := by
  obtain ⟨-, -, -, hv, -⟩ := diameter_three_rank_five_of_ambient ambientRootOrbitsHyp
  obtain ⟨-, cN, cT3, cT4, cD3, -⟩ := hv v
  match k with
  | 0 => exact cN
  | 1 => exact cD3
  | 2 => exact cT3
  | 3 => exact cT4

theorem labelSphere_trans
    {k : Fin 4} {v u u' : CVert} (hu : u ∈ labelSphere k v)
    (hu' : u' ∈ labelSphere k v) :
    ∃ s : Shat, s * clabelS v = clabelS v * s ∧ s⁻¹ * clabelS u * s = clabelS u' := by
  obtain ⟨-, -, -, hv, -⟩ := diameter_three_rank_five_of_ambient ambientRootOrbitsHyp
  obtain ⟨-, -, -, -, -, oN, oT3, oT4, oD3⟩ := hv v
  have horb : vStabOrbit v u = labelSphere k v := by
    match k, hu with
    | 0, hu => exact oN u hu
    | 1, hu => exact oD3 u hu
    | 2, hu => exact oT3 u hu
    | 3, hu => exact oT4 u hu
  obtain ⟨s, hs, hsu⟩ : u' ∈ vStabOrbit v u := horb ▸ hu'
  refine ⟨s, ?_, by rw [← hsu, clabelS_cvMul]⟩
  have e := clabelS_cvMul v s
  rw [hs] at e
  calc s * clabelS v = s * (s⁻¹ * clabelS v * s) := by rw [← e]
    _ = clabelS v * s := by group

theorem isConj_clabelS_mul_of_mem_zero
    {v u : CVert} (hu : u ∈ labelSphere 0 v) :
    IsConj (clabelS v * clabelS u) CTIB.xhatS :=
  CTIB.isConj_clabelS_mul_of_adj hu

theorem isConj_clabelS_mul_of_mem_one
    {v u : CVert} (hu : u ∈ labelSphere 1 v) :
    IsConj (clabelS v * clabelS u) (CTIB.sEquiv (CTIB.rs 5)) := by
  obtain ⟨⟨v₁, u₁, hd₁, hc₁⟩, -⟩ := CTIB.native_rank_2158_distance_three_product_final
  obtain ⟨-, -, -, hv, -⟩ := diameter_three_rank_five_of_ambient ambientRootOrbitsHyp
  obtain ⟨-, -, -, -, -, -, -, -, oD3⟩ := hv v
  obtain ⟨g₁, hg₁⟩ := cvMul_transitive v₁ v
  have hu₁ : cvMul u₁ g₁ ∈ sphereDistThree v := by
    rw [mem_sphereDistThree, ← hg₁, dist_cvMul]
    exact hd₁
  obtain ⟨g₂, hg₂, hg₂u⟩ : u ∈ vStabOrbit v (cvMul u₁ g₁) := by
    rw [oD3 _ hu₁]
    exact hu
  have e1 := clabelS_cvMul v₁ (g₁ * g₂)
  have e2 := clabelS_cvMul u₁ (g₁ * g₂)
  rw [cvMul_mul, hg₁, hg₂] at e1
  rw [cvMul_mul, hg₂u] at e2
  rw [e1, e2]
  have e : (g₁ * g₂)⁻¹ * clabelS v₁ * (g₁ * g₂) * ((g₁ * g₂)⁻¹ * clabelS u₁ * (g₁ * g₂)) =
      (g₁ * g₂)⁻¹ * (clabelS v₁ * clabelS u₁) * (g₁ * g₂) := by group
  rw [e]
  exact (isConj_iff.2 ⟨g₁ * g₂, by group⟩ : IsConj ((g₁ * g₂)⁻¹ * (clabelS v₁ * clabelS u₁) *
    (g₁ * g₂)) (clabelS v₁ * clabelS u₁)).trans hc₁.symm

theorem orderOf_clabelS_mul_of_mem_two
    {v u : CVert} (hu : u ∈ labelSphere 2 v) :
    orderOf (clabelS v * clabelS u) = 3 := by
  rw [CTIB.orderOf_clabelS_mul]
  exact ((native_order_three_label_products_and_dihedral_triples v).1 u hu).1

theorem orderOf_clabelS_mul_of_mem_three
    {v u : CVert} (hu : u ∈ labelSphere 3 v) :
    orderOf (clabelS v * clabelS u) = 4 := by
  rw [CTIB.orderOf_clabelS_mul]
  exact (native_coset_graph_order_four_common_neighbors.1 v u hu).1

theorem isConj_sq_clabelS_mul_of_mem_three
    {v u : CVert} (hu : u ∈ labelSphere 3 v) :
    IsConj ((clabelS v * clabelS u) ^ 2) CTIB.xhatS := by
  obtain ⟨s, hvs, hus⟩ := (native_coset_graph_order_four_common_neighbors.1 v u hu).2.2.1
  have h := CTIB.sq_clabel_mul_of_mem_cPi hu hvs hus
  refine isConj_iff.2 ⟨s, Subtype.ext ?_⟩
  have e : (((clabelS v * clabelS u) ^ 2 : Shat) : Dfull) = ((s : Dfull))⁻¹ * xhat * s := by
    rw [Subgroup.coe_pow, Subgroup.coe_mul, coe_clabelS, coe_clabelS]
    exact h
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, e]
  show (s : Dfull) * ((s : Dfull)⁻¹ * xhat * s) * (s : Dfull)⁻¹ = xhat
  group

end CFSG.Monster.Existence
