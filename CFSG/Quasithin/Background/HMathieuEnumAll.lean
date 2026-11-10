module

public import CFSG.Quasithin.Background.HMathieuEnum

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.QuasithinUnique.Setup.X1

variable {P : Type*} [Group P] [DecidableEq P]

@[expose] def forallGreedyAll (posF : P → ℕ) (Rinv : List P) (pred : List P → Bool) :
    ℕ → List P → Bool
  | 0, l => pred l
  | k + 1, l =>
    pred l && (greedyExtP posF Rinv l).all fun x => forallGreedyAll posF Rinv pred k (x :: l)

theorem forallGreedyAll_le {posF : P → ℕ} {Rinv : List P} {pred : List P → Bool} :
    ∀ (k : ℕ) (l : List P), forallGreedyAll posF Rinv pred k l = true →
      ∀ j ≤ k, forallGreedyP posF Rinv pred j l = true
  | 0, l, h, j, hj => by
    obtain rfl : j = 0 := by omega
    exact h
  | k + 1, l, h, j, hj => by
    rw [forallGreedyAll, Bool.and_eq_true, List.all_eq_true] at h
    rcases j with _ | j
    · exact h.1
    · rw [forallGreedyP, List.all_eq_true]
      exact fun x hx => forallGreedyAll_le k (x :: l) (h.2 x hx) j (by omega)


end CFSG.Quasithin.H.Mathieu
