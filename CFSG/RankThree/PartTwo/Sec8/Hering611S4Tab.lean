module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.SmallOddCore.J3CheckInputs

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

abbrev Gp : Type := Equiv.Perm (Fin 6156)


@[expose] def prodG (Rg : ℕ → Gp) (l : List ℕ) : Gp := (l.map Rg).prod

@[expose] def Ksub (Rg : ℕ → Gp) (gi : List ℕ) : Subgroup Gp :=
  closure (Rg '' {r | r ∈ gi})

inductive TFact where
  | eqP (l₁ l₂ : List ℕ)
  | neP (l₁ l₂ : List ℕ)
  | memE (e : ℕ) (l : List ℕ)
  | inP (l : List ℕ)
  | notInP (l : List ℕ)
  | ordEq (i m : ℕ)
  deriving DecidableEq


@[expose] noncomputable def TFact.sem (Rg : ℕ → Gp) (K : ℕ → Subgroup Gp) : TFact → Prop
  | .eqP l₁ l₂ => prodG Rg l₁ = prodG Rg l₂
  | .neP l₁ l₂ => prodG Rg l₁ ≠ prodG Rg l₂
  | .memE e l => prodG Rg l ∈ K e
  | .inP l => prodG Rg l ∈ j3P
  | .notInP l => prodG Rg l ∉ j3P
  | .ordEq i m => orderOf (Rg i) = m

inductive Cond where
  | comm (r : ℕ)
  | commM (w r : ℕ)
  | memConj (e r : ℕ)
  | memSelf (e : ℕ)
  | not (c : Cond)
  | and (c d : Cond)
  | imp (c d : Cond)
  deriving DecidableEq

@[expose] def Cond.wfB (nR nE : ℕ) : Cond → Bool
  | .comm r => decide (r < nR)
  | .commM w r => decide (w < nR) && decide (r < nR)
  | .memConj e r => decide (e < nE) && decide (r < nR)
  | .memSelf e => decide (e < nE)
  | .not c => c.wfB nR nE
  | .and c d => c.wfB nR nE && d.wfB nR nE
  | .imp c d => c.wfB nR nE && d.wfB nR nE


@[expose] noncomputable def Cond.sem (Rg : ℕ → Gp) (K : ℕ → Subgroup Gp) (x : Gp) : Cond → Prop
  | .comm r => x * Rg r = Rg r * x
  | .commM w r => (x * Rg w) * Rg r = Rg r * (x * Rg w)
  | .memConj e r => x * Rg r * x⁻¹ ∈ K e
  | .memSelf e => x ∈ K e
  | .not c => ¬ c.sem Rg K x
  | .and c d => c.sem Rg K x ∧ d.sem Rg K x
  | .imp c d => c.sem Rg K x → d.sem Rg K x

inductive TLoop where
  | allE (e : ℕ) (c : Cond)
  | countEq (e : ℕ) (c : Cond) (b : ℕ)
  | countLe (e : ℕ) (c : Cond) (b : ℕ)
  | exE (e : ℕ) (c : Cond)
  deriving DecidableEq


@[expose] noncomputable def TLoop.sem (Rg : ℕ → Gp) (K : ℕ → Subgroup Gp) : TLoop → Prop
  | .allE e c => ∀ x ∈ K e, c.sem Rg K x
  | .countEq e c b => Set.ncard {x | x ∈ K e ∧ c.sem Rg K x} = b
  | .countLe e c b => Set.ncard {x | x ∈ K e ∧ c.sem Rg K x} ≤ b
  | .exE e c => ∃ x ∈ K e, c.sem Rg K x

structure TData where
  prog : List Instr
  enums : List (List ℕ × ℕ)
  facts : List TFact
  loops : List TLoop
  fixedBelow : ℕ

structure TSem (initG Rg : ℕ → Gp) (D : TData) : Prop where
  fixed : ∀ r < D.fixedBelow, Rg r = initG r
  card : ∀ e (he : e < D.enums.length), Nat.card (Ksub Rg D.enums[e].1) = D.enums[e].2
  fact : ∀ f ∈ D.facts, f.sem Rg (fun e => Ksub Rg (D.enums[e]!).1)
  loop : ∀ l ∈ D.loops, l.sem Rg (fun e => Ksub Rg (D.enums[e]!).1)

theorem TSem.fact_get {initG Rg : ℕ → Gp} {D : TData} (h : TSem initG Rg D) (k : ℕ)
    (hk : k < D.facts.length) : D.facts[k].sem Rg (fun e => Ksub Rg (D.enums[e]!).1) :=
  h.fact _ (List.getElem_mem hk)

theorem TSem.loop_get {initG Rg : ℕ → Gp} {D : TData} (h : TSem initG Rg D) (k : ℕ)
    (hk : k < D.loops.length) : D.loops[k].sem Rg (fun e => Ksub Rg (D.enums[e]!).1) :=
  h.loop _ (List.getElem_mem hk)

end CFSG.RankThree.PartTwo.Sec8.Hering611.J3T
