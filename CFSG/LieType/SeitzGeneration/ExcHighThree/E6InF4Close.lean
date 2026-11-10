module

public import CFSG.HardMathSupport.Lang.AnisoE6.ThirdA2Fixed
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Glue

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6

section Fixed


end Fixed

section Closing


theorem closure_conj_eq_top (K : Type) [Field K] (R : Subgroup (adjointGroup .E6 K))
    (k : adjointGroup .E6 K) (hk : k ∈ R) (z : adjointGroup .E6 K)
    (h : Subgroup.closure ((R : Set (adjointGroup .E6 K)) ∪
      (Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))) = ⊤) :
    Subgroup.closure ((R : Set (adjointGroup .E6 K)) ∪
      (Subgroup.centralizer ({k⁻¹ * z * k} : Set (adjointGroup .E6 K)) :
        Set (adjointGroup .E6 K))) = ⊤ := by
  classical
  set M := Subgroup.closure ((R : Set (adjointGroup .E6 K)) ∪
      (Subgroup.centralizer ({k⁻¹ * z * k} : Set (adjointGroup .E6 K)) :
        Set (adjointGroup .E6 K))) with hM
  have hconj : ∀ x ∈ Subgroup.closure ((R : Set (adjointGroup .E6 K)) ∪
      (Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))),
      k⁻¹ * x * k ∈ M := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hxR | hxC
      · apply Subgroup.subset_closure
        left
        have : k⁻¹ * x * k ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hk) hxR) hk
        exact this
      · apply Subgroup.subset_closure
        right
        simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
          forall_eq] at hxC ⊢
        calc k⁻¹ * z * k * (k⁻¹ * x * k) = k⁻¹ * (z * x) * k := by group
          _ = k⁻¹ * (x * z) * k := by rw [hxC]
          _ = (k⁻¹ * x * k) * (k⁻¹ * z * k) := by group
    | one => simp
    | mul x y _ _ hx hy =>
      have : k⁻¹ * (x * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by group
      rw [this]
      exact M.mul_mem hx hy
    | inv x _ hx =>
      have : k⁻¹ * x⁻¹ * k = (k⁻¹ * x * k)⁻¹ := by group
      rw [this]
      exact M.inv_mem hx
  rw [eq_top_iff]
  intro y _
  have hy : k * y * k⁻¹ ∈ Subgroup.closure ((R : Set (adjointGroup .E6 K)) ∪
      (Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))) := by
    rw [h]
    exact Subgroup.mem_top _
  have := hconj _ hy
  have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
  rwa [e] at this

section Glue


theorem exists_units_orderOf_three (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1) :
    ∃ ω : Kˣ, orderOf ω = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hdvd : 3 ∣ Fintype.card Kˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units]
    have h1 : 1 ≤ Nat.card K := Nat.card_pos
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  exact ⟨ω, hω⟩


end Glue

end Closing

end CFSG.LieType.SeitzGeneration.ExcHighThree

end
