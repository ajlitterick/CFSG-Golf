module

public import CFSG.LocalAnalysis.ComponentInitial.OddCoreQuotient
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem exists_isPComponent_of_isComponent {X : Type*} [Group X] [Finite X] (p : ℕ)
    {K : Subgroup (X ⧸ pPrimeCore p X)} (hK : IsComponent K) :
    ∃ L : Subgroup X, IsPComponent p L ∧ L.map (QuotientGroup.mk' (pPrimeCore p X)) = K := by
  set π := QuotientGroup.mk' (pPrimeCore p X)
  set S : Set (Subgroup X) := {L | L.IsSubnormal ∧ L.map π = K}
  have hS : S.Nonempty := ⟨K.comap π, hK.2.comap π,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) K⟩
  obtain ⟨L, hL⟩ := (Set.toFinite S).exists_minimal hS
  refine ⟨L, ⟨K, hK, hL.1.1, hL.1.2, fun J hJL hJsub hJmap => ?_⟩, hL.1.2⟩
  exact not_le_of_gt hJL (hL.2 ⟨hJsub, hJmap⟩ hJL.le)

theorem ne_bot_of_isComponent {X : Type*} [Group X] {K : Subgroup X} (hK : IsComponent K) :
    K ≠ ⊥ := by
  have := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  exact (Subgroup.nontrivial_iff_ne_bot K).1 this


end CFSG.LocalAnalysis.ComponentInitial
