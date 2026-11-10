module

public import CFSG.ClassicalInvolution.Q3.Q3CPThin
public import CFSG.ClassicalInvolution.SmallCases.NDBH2
public import CFSG.ClassicalInvolution.Q3.Q3CPSat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Asc77

section Defs

@[expose] def L67Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)),
    Disconnected.AschTight.HypOmegaGen Ω →
    ∀ S : Sylow 2 G, ∀ R ∈ RSet Ω, ∀ R' ∈ RSet Ω, R ≤ (S : Subgroup G) → R' ≤ (S : Subgroup G) →
      R ≠ R' → Commutes R R'


end Defs

section Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_W_of_hypOmegaGen {Ω : Set (Subgroup G)}
    (hgen : Disconnected.AschTight.HypOmegaGen Ω) (S : Sylow 2 G) :
    ∃ W : Subgroup G, W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧
      ∀ s ∈ (S : Subgroup G), conjSub s W = W := by
  obtain ⟨η, hη, hηinv⟩ :=
    Disconnected.AschTight.Sec6Gen.exists_invariant_mem_etaSet hgen S
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((⨆ U ∈ η, U : Subgroup G) : Set G) :=
    Thompson.le_normalizer_biSup_of_acts hηinv
  exact ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hηinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2,
    fun s hs' => mem_normalizer_iff_conjSub_eq.mp (hSN hs')⟩


theorem eq_of_isSylow2In_of_le_sylow' {M P Q : Subgroup G} {S : Sylow 2 G}
    (hP : IsSylow2In P M) (hQ : IsSylow2In Q M) (hPS : P ≤ (S : Subgroup G))
    (hQS : Q ≤ (S : Subgroup G)) : P = Q := by
  have h1 : M ⊓ (S : Subgroup G) = P :=
    hP.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hP.1 hPS)
  have h2 : M ⊓ (S : Subgroup G) = Q :=
    hQ.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hQ.1 hQS)
  exact h1.symm.trans h2

end Generic

section Branch


end Branch

section Loc26


end Loc26

section Final


end Final


end CFSG.ClassicalInvolution.Q3.Q3CP
