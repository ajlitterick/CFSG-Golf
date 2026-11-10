module

public import CFSG.ClassicalInvolution.Q3.Q3YSTwin

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank


@[expose] def ModelFourGroup3On (S : StatedLieTag → Prop) : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), S t → IsFundTag t → StatedLieAdmissible t n 3 1 →
    ¬ (t = .PSp ∧ n = 2) → Even (Nat.card (modelUniv t n 3 1 Nat.prime_three).K) →
    ∃ F : Subgroup (modelUniv t n 3 1 Nat.prime_three).K, IsElemAbelian 2 F ∧ Nat.card F = 4 ∧
      F ⊓ Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K = ⊥


theorem ModelFourGroup3On.mono {S S' : StatedLieTag → Prop} (h : ModelFourGroup3On S)
    (hle : ∀ t, S' t → S t) : ModelFourGroup3On S' :=
  fun t n ht => h t n (hle t ht)

theorem ModelFourGroup3On.union {S S' : StatedLieTag → Prop} (h : ModelFourGroup3On S)
    (h' : ModelFourGroup3On S') : ModelFourGroup3On fun t => S t ∨ S' t :=
  fun t n ht => ht.elim (h t n) (h' t n)


end CFSG.ClassicalInvolution.Q3.Q3YS
