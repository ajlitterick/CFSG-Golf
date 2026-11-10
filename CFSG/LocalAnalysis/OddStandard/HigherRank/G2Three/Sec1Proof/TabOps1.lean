module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {D : TabData} {elt : ℕ → Γ}


@[expose] def topB (D : TabData) : BSet := BSet.ofFn D.n fun _ => true


end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
