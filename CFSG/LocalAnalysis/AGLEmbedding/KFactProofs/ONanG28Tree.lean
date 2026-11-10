module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Check
public import Std.Data.HashSet.Lemmas
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.RankThree.PartTwo.Sec4.Item434G28

@[expose] def invDiag (u : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 36) fun t => if t.val % 7 = 0 then u[t.val]! ^^^ 1 else u[t.val]!

@[expose] def canonCode (u : Array ℕ) : Array ℕ := if u[0]! % 2 = 0 then u else invDiag u

@[expose] def conjCode (g gi c : Array ℕ) : Array ℕ := mulCode (mulCode g c) gi

structure TreeData where
  R : ℕ
  N : ℕ
  roots : Array (Array ℕ)
  gens : Array (Array ℕ)
  ginvs : Array (Array ℕ)
  par : ℕ → ℕ
  sym : ℕ → ℕ

namespace TreeData

@[expose] def step (D : TreeData) (acc : Array (Array ℕ × ℕ)) (n : ℕ) : Array ℕ × ℕ :=
  if n < D.R then (D.roots[n]!, n) else
    (canonCode (conjCode D.gens[D.sym n]! D.ginvs[D.sym n]! (acc[D.par n]!).1), (acc[D.par n]!).2)


end TreeData


end CFSG.AGLEmbedding.KFactProofs.G28
