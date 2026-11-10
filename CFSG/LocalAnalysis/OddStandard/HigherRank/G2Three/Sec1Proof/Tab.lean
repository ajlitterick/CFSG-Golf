module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open scoped commutatorElement

abbrev BSet : Type := Array Bool

namespace BSet


@[expose] def ofFn (n : ℕ) (f : ℕ → Bool) : BSet := (Array.range n).map f


end BSet

structure TabData where
  n : ℕ
  rows : Array (Array ℕ)
  invs : Array ℕ

namespace TabData

@[expose] def mul (D : TabData) (i j : ℕ) : ℕ := (D.rows.getD i #[]).getD j 0

@[expose] def inv (D : TabData) (i : ℕ) : ℕ := D.invs.getD i 0


@[expose] def conj (D : TabData) (c x : ℕ) : ℕ := D.mul (D.mul c x) (D.inv c)

@[expose] def comm (D : TabData) (x y : ℕ) : ℕ := D.mul (D.mul (D.mul x y) (D.inv x)) (D.inv y)

end TabData


namespace Realizes


end Realizes


namespace Rep


end Rep

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
