module

public import CFSG.ClassicalInvolution.Q3.ExactDelta
public import CFSG.ClassicalInvolution.Q3.LocalOddCentral
public import CFSG.ClassicalInvolution.Q3.TripleBalance
public import CFSG.ClassicalInvolution.Balance.BootstrapAlphaDelta

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem group_le_centralizingLayer_of_exactTriple {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω) {b : G}
    (hb : b ∈ T.group) : T.group ≤ centralizingLayer Ω {b} := by
  have hbK : ∀ {K : Subgroup G}, K ≤ Subgroup.centralizer (T.group : Set G) →
      K ≤ Subgroup.centralizer ({b} : Set G) := fun hK =>
    hK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
  have h1 : K₁ ≤ centralizingLayer Ω {b} := le_centralizingLayer ⟨hΩ₁, hbK T.le_centralizer₁⟩
  have h2 : K₂ ≤ centralizingLayer Ω {b} := le_centralizingLayer ⟨hΩ₂, hbK T.le_centralizer₂⟩
  have h3 : K₃ ≤ centralizingLayer Ω {b} := le_centralizingLayer ⟨hΩ₃, hbK T.le_centralizer₃⟩
  refine (Subgroup.closure_le _).mpr ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  exacts [h1 T.mem₁, h2 T.mem₂, h3 T.mem₃]


end CFSG.ClassicalInvolution.Q3
