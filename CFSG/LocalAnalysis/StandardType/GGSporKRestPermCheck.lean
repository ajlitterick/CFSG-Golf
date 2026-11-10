module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestEval
public import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

namespace CFSG.StandardType.SporadicShape.PermCover

open Equiv

structure Entry where
  idx : ℕ
  h : String
  zs : List String

structure ClassData where
  x : String
  ent : List Entry
  wa : String
  wb : String

structure CensusEntry where
  t : ℕ
  cls : ℕ
  g : String

structure Data where
  sgW : List String
  tabW : List String
  classes : List ClassData
  census : List CensusEntry

@[expose] def sg {n : ℕ} (a b : Perm (Fin n)) (d : Data) : List (Perm (Fin n)) :=
  d.sgW.map fun w => sporKRestEval [a, b] (sporKRestParse w)

@[expose] def tab {n : ℕ} (a b : Perm (Fin n)) (d : Data) : List (Perm (Fin n)) :=
  d.tabW.map fun w => sporKRestEval (sg a b d) (sporKRestParse w)

@[expose] def rep {n : ℕ} (a b : Perm (Fin n)) (c : ClassData) : Perm (Fin n) := sporKRestEval [a, b] (sporKRestParse c.x)

@[expose] def letters {n : ℕ} (a b : Perm (Fin n)) (d : Data) (c : ClassData) : List (Perm (Fin n)) :=
  sg a b d ++ c.ent.flatMap fun e => e.zs.map fun w => sporKRestEval [a, b] (sporKRestParse w)

@[expose] def spec {n : ℕ} (a b : Perm (Fin n)) (sylowOrder : ℕ) (d : Data) : Prop :=
  (tab a b d).length = sylowOrder ∧ (tab a b d).Nodup ∧ (1 : Perm (Fin n)) ∈ tab a b d ∧
  (∀ t ∈ tab a b d, ∀ g ∈ sg a b d, t * g ∈ tab a b d ∧ t * g⁻¹ ∈ tab a b d) ∧
  (∀ c ∈ d.classes,
    (∀ e ∈ c.ent, e.idx < (tab a b d).length ∧
      (sporKRestEval [a, b] (sporKRestParse e.h))⁻¹ * rep a b c * sporKRestEval [a, b] (sporKRestParse e.h) = (tab a b d).getD e.idx 1 ∧
      ∀ zw ∈ e.zs, sporKRestEval [a, b] (sporKRestParse zw) * (tab a b d).getD e.idx 1 =
        (tab a b d).getD e.idx 1 * sporKRestEval [a, b] (sporKRestParse zw)) ∧
    sporKRestEval (letters a b d c) (sporKRestParse c.wa) = a ∧ sporKRestEval (letters a b d c) (sporKRestParse c.wb) = b) ∧
  (∀ t ∈ tab a b d, t ≠ 1 → ∃ e ∈ d.census, e.cls < d.classes.length ∧ (tab a b d).getD e.t 1 = t ∧
    (sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ * rep a b (d.classes.getD e.cls ⟨"", [], "", ""⟩) *
      sporKRestEval [a, b] (sporKRestParse e.g) = t)

@[expose] def check {n : ℕ} (a b : Perm (Fin n)) (sylowOrder : ℕ) (d : Data) : Bool :=
  let sg := sg a b d
  let tab := tab a b d
  decide (tab.length = sylowOrder) && decide tab.Nodup && decide ((1 : Perm (Fin n)) ∈ tab) &&
  tab.all (fun t => sg.all fun g => decide (t * g ∈ tab) && decide (t * g⁻¹ ∈ tab)) &&
  d.classes.all (fun c =>
    c.ent.all (fun e => decide (e.idx < tab.length) &&
      decide ((sporKRestEval [a, b] (sporKRestParse e.h))⁻¹ * rep a b c * sporKRestEval [a, b] (sporKRestParse e.h) = tab.getD e.idx 1) &&
      e.zs.all fun zw => decide (sporKRestEval [a, b] (sporKRestParse zw) * tab.getD e.idx 1 =
        tab.getD e.idx 1 * sporKRestEval [a, b] (sporKRestParse zw))) &&
    decide (sporKRestEval (letters a b d c) (sporKRestParse c.wa) = a) &&
    decide (sporKRestEval (letters a b d c) (sporKRestParse c.wb) = b)) &&
  tab.all (fun t => decide (t = 1) || d.census.any fun e => decide (e.cls < d.classes.length) &&
    decide (tab.getD e.t 1 = t) &&
    decide ((sporKRestEval [a, b] (sporKRestParse e.g))⁻¹ * rep a b (d.classes.getD e.cls ⟨"", [], "", ""⟩) *
      sporKRestEval [a, b] (sporKRestParse e.g) = t))


end CFSG.StandardType.SporadicShape.PermCover
