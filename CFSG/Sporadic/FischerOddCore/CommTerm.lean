module

public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped commutatorElement

inductive CommTerm where
  | leaf (i : ℕ)
  | comm (a b : CommTerm)

namespace CommTerm

@[expose] def eval {G : Type*} [Group G] (f : ℕ → G) : CommTerm → G
  | leaf i => f i
  | comm a b => ⁅eval f a, eval f b⁆

@[expose] def depth : CommTerm → ℕ
  | leaf _ => 0
  | comm a b => min (depth a) (depth b) + 1


theorem derivedSeries_antitone {G : Type*} [Group G] {m n : ℕ} (h : m ≤ n) :
    derivedSeries G n ≤ derivedSeries G m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    refine le_trans ?_ ih
    rw [derivedSeries_succ]
    exact Subgroup.commutator_le_left _ _


end CommTerm

end CFSG.Sporadic.FischerOddCore
