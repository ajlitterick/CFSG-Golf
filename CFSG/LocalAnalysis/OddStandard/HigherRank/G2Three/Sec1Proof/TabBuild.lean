module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabOps1
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

structure GenData where
  n : ℕ
  ng : ℕ
  rt : Array (Array ℕ)
  par : Array (ℕ × ℕ)

namespace GenData

@[expose] def rtAt (G : GenData) (i s : ℕ) : ℕ := (G.rt.getD i #[]).getD s 0

@[expose] def parAt (G : GenData) (j : ℕ) : ℕ × ℕ := G.par.getD (j - 1) (0, 0)

@[expose] def walk {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α) : Array α :=
  (List.range G.n).foldl (fun acc j =>
    if j == 0 then acc.push one else acc.push (step (acc.getD (G.parAt j).1 one) (G.parAt j).2))
    #[]


@[expose] def rowOf (G : GenData) (i : ℕ) : Array ℕ := G.walk i G.rtAt

@[expose] def rowsOf (G : GenData) : Array (Array ℕ) := (Array.range G.n).map G.rowOf

@[expose] def invsOf (G : GenData) (rs : Array (Array ℕ)) : Array ℕ :=
  (Array.range G.n).map fun i =>
    ((List.range G.n).find? fun j => (rs.getD i #[]).getD j 0 == 0).getD 0

@[expose] def tab (G : GenData) : TabData :=
  let rs := G.rowsOf
  ⟨G.n, rs, G.invsOf rs⟩


end GenData

open GenData


end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
