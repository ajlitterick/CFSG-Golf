module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL310

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G]

@[expose] def SigPair (N K K' V B : Subgroup G) : Prop :=
  K ∈ kStarComponents N ∧ K' ∈ kStarComponents N ∧ K ≠ K' ∧ IsKleinFour V ∧ V ≤ K' ∧
    B ≤ coreActionKernel K' ∧ B ≤ centralizer (V : Set G) ∧ CFSG.Open.IsElemAbelian 2 B ∧
    Nat.card B = 8 ∧ B ≤ N ∧ ∃ E : Subgroup G, IsKleinFour E ∧ E ≤ B ∧ E ≤ K


@[expose] def SingleComponentExcludedFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      (∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G)) →
      (∀ K'' ∈ kStarComponents N, ∀ s ∈ K'', orderOf s = 2 →
        twoLayerIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G)) →
      ∀ M : Subgroup G, IsTwoComponentIn M (normalizer (wGroup B V : Set G)) →
        ¬ ∀ K'' ∈ kStarComponents N, K'' ≤ M


theorem oddCoreIn_inf_le_wGroup {V B : Subgroup G} (hV : IsKleinFour V)
    (hBV : B ≤ centralizer (V : Set G)) {e f : G} (heB : e ∈ B) (he1 : e ≠ 1) (hfV : f ∈ V) :
    oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) ≤
      wGroup B V := by
  have h1 : oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) ≤
      theta (zpowers f) e := by
    rw [theta, centralizer_zpowers_eq]
    exact le_sup_right
  exact h1.trans ((theta_mono (zpowers_le.mpr hfV) (isPGroup_of_isKleinFour hV)
    (comm_of_isKleinFour hV) (le_centralizer_singleton_of_mem hBV heB)).trans
      (theta_le_wGroup heB he1))


end CFSG.ComponentClassification.Sol76.Sig
