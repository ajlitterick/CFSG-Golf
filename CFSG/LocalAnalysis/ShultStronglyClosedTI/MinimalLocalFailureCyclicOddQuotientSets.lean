module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicOddQuotientLift

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CyclicPair.OddQuotient

universe u v

variable {E : Type u} {F : Type v} [Group E] [Group F]


theorem subgroup_involution_bijOn (eta : E →* F) (hsurj : Function.Surjective eta)
    (hcentral : eta.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card eta.ker))
    (M : Subgroup E) (hker : eta.ker ≤ M) :
    Set.BijOn eta {x : E | x ∈ M ∧ orderOf x = 2}
      {y : F | y ∈ M.map eta ∧ orderOf y = 2} := by
  refine Set.BijOn.mk ?_ ?_ ?_
  · intro x hx
    exact ⟨Subgroup.mem_map_of_mem eta hx.1, map_involution eta hodd hx.2⟩
  · intro x hx w hw heq
    exact involution_lifts_injective eta hcentral hodd hx.2 hw.2 heq
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := exists_involution_lift eta hsurj hcentral hodd hy.2
    have hxM : x ∈ M := by
      have hxpre : x ∈ (M.map eta).comap eta := by
        change eta x ∈ M.map eta
        rw [hxy]
        exact hy.1
      rw [Subgroup.comap_map_eq_self hker] at hxpre
      exact hxpre
    exact ⟨x, ⟨hxM, hx⟩, hxy⟩


@[expose] def subgroupInvolutionEquiv (eta : E →* F) (hsurj : Function.Surjective eta)
    (hcentral : eta.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card eta.ker))
    (M : Subgroup E) (hker : eta.ker ≤ M) :
    {x : E | x ∈ M ∧ orderOf x = 2} ≃
      {y : F | y ∈ M.map eta ∧ orderOf y = 2} :=
  (subgroup_involution_bijOn eta hsurj hcentral hodd M hker).equiv eta


theorem subgroup_involution_card (eta : E →* F) (hsurj : Function.Surjective eta)
    (hcentral : eta.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card eta.ker))
    (M : Subgroup E) (hker : eta.ker ≤ M) :
    Nat.card {x : E | x ∈ M ∧ orderOf x = 2} =
      Nat.card {y : F | y ∈ M.map eta ∧ orderOf y = 2} :=
  Nat.card_congr (subgroupInvolutionEquiv eta hsurj hcentral hodd M hker)

end CFSG.ShultStronglyClosedTI.CyclicPair.OddQuotient
