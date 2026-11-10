module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClLink
public import CFSG.LocalAnalysis.StandardType.GGSporKRestDistinctDefs

public section

namespace CFSG.StandardType.SporadicShape

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem sporKRest_complete_of_distinct {K : Type} [Group K] {p N : ℕ} (ρ : Fin N → K)
    (hlib : ∀ s : K, orderOf s = p → ∃ k, IsConj s (ρ k)) (r : Fin N → K)
    (hord : ∀ j, orderOf (r j) = p) (hnc : ∀ j j', IsConj (r j) (r j') → j = j') :
    ∀ s : K, orderOf s = p → ∃ j, IsConj (r j) s := by
  have hex : ∀ j, ∃ k, IsConj (r j) (ρ k) := fun j => by
    obtain ⟨k, hk⟩ := hlib (r j) (hord j)
    exact ⟨k, hk⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro j j' h
    apply hnc
    refine (hf j).trans ?_
    rw [h]
    exact (hf j').symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro s hs
  obtain ⟨k, hk⟩ := hlib s hs
  obtain ⟨j, rfl⟩ := hsurj k
  exact ⟨j, (hf j).trans hk.symm⟩

namespace PermCover


end PermCover


end CFSG.StandardType.SporadicShape
