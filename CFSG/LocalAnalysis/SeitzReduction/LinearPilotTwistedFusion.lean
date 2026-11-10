module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionGraphAlt
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionGraphFive

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.SeitzReduction.F4Pilot (PerfectTwistedFusion)

variable {K : Type} [Field K] {n : ℕ}

@[expose] def IsTransvectionOrJ2 (y : projectiveSL n K) : Prop :=
  IsInvolutionClass 1 y ∨ IsInvolutionClass 2 y

theorem IsTransvectionOrJ2.conjAut {y : projectiveSL n K} (h : IsTransvectionOrJ2 y)
    (A : GL (Fin n) K) : IsTransvectionOrJ2 (LinearFlag.conjAut n K A y) :=
  h.imp (fun h1 => h1.conjAut A) (fun h2 => h2.conjAut A)


end CFSG.SeitzReduction.LinearPilot
