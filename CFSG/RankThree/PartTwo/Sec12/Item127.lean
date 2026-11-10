module

public import CFSG.RankThree.PartTwo.KFacts.KS127Exc
import CFSG.RankThree.PartTwo.Sec12.Item124Bar
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec12.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_theta_of_ne {b : G} {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ thetaComponentsAt 3 b) (h₂ : K₂ ∈ thetaComponentsAt 3 b) (hne : K₁ ≠ K₂)
    {x y : G} (hx : x ∈ K₁) (hy : y ∈ K₂) :
    x * y * x⁻¹ * y⁻¹ ∈
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨K₁', hK₁', rfl⟩ := h₁
  obtain ⟨K₂', hK₂', rfl⟩ := h₂
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence
    (H := Subgroup.centralizer ({b} : Set G)) Nat.prime_three
  set π := QuotientGroup.mk'
    (aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set G))) with hπ
  have hne' : K₁' ≠ K₂' := fun h => hne (h ▸ rfl)
  have hJne : K₁'.map π ≠ K₂'.map π := fun h => hne' (hbij.injOn hK₁' hK₂' h)
  have hcomm := (LocalCores.distinct_components_commute
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hK₁')
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hK₂')).resolve_left hJne
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have h1 : π y' * π x' = π x' * π y' :=
    Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_map_of_mem π hx')) _
      (Subgroup.mem_map_of_mem π hy')
  have h2 : π (x' * y' * x'⁻¹ * y'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
    group
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact ⟨_, h2, rfl⟩

theorem mem_thetaQuotCentralizer_of_ne {b : G} {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ thetaComponentsAt 3 b) (h₂ : K₂ ∈ thetaComponentsAt 3 b) (hne : K₁ ≠ K₂)
    {x : G} (hx : x ∈ K₁) (hxN : x ∈ Subgroup.normalizer (K₂ : Set G)) :
    x ∈ Sec4.thetaQuotCentralizer K₂ := by
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hxN, fun l hl => ?_⟩
  rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt h₂]
  refine ⟨K₂.mul_mem (K₂.inv_mem hl) ((Subgroup.mem_normalizer_iff.mp hxN l).mp hl), ?_⟩
  have hlC : l⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
    inv_mem (Sec6.le_centralizer_of_mem_thetaComponentsAt h₂ hl)
  have h1 := Sec13.conj_mem_inSubgroup_theta hlC (commutator_mem_theta_of_ne h₁ h₂ hne hx hl)
  have e : l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (x * l * x⁻¹) := by group
  rwa [e] at h1

theorem mem_thetaQuotCentralizer_of_sup_eq {L K : Subgroup G} (hLK : L ≤ K)
    (hsup : L ⊔ inSubgroup (aschbacherSolvableCore 3) K = K) {x : G}
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hxL : x ∈ Subgroup.centralizer (L : Set G)) :
    x ∈ Sec4.thetaQuotCentralizer K := by
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hxN, fun k hk => ?_⟩
  have hLN : L ≤ Subgroup.normalizer
      ((inSubgroup (aschbacherSolvableCore 3) K : Subgroup G) : Set G) := fun l hl =>
    Subgroup.mem_normalizer_fintype fun g hg => Sec13.conj_mem_inSubgroup_theta (hLK hl) hg
  have hk' : k ∈ ((L ⊔ inSubgroup (aschbacherSolvableCore 3) K : Subgroup G) : Set G) := by
    rw [hsup]
    exact hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLN] at hk'
  obtain ⟨l, hl, n, hn, rfl⟩ := hk'
  have hxl : x * l = l * x := (Subgroup.mem_centralizer_iff.mp hxL l hl).symm
  have h1 := conj_mem_inSubgroup_theta hxN hn
  have e : (l * n)⁻¹ * (x * (l * n) * x⁻¹) = n⁻¹ * (x * n * x⁻¹) := by
    calc (l * n)⁻¹ * (x * (l * n) * x⁻¹) = n⁻¹ * l⁻¹ * ((x * l) * n * x⁻¹) := by group
      _ = n⁻¹ * l⁻¹ * ((l * x) * n * x⁻¹) := by rw [hxl]
      _ = n⁻¹ * (x * n * x⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) h1


end CFSG.RankThree.PartTwo.Sec12
