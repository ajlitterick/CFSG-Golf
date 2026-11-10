module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ShortExtractNoT

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups commutatorElement

section ExtractUNoT


variable {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)

@[expose] def HasShortRoot (H : Subgroup (twistedGroup σ.toRingHom)) : Prop :=
  ∃ k : ℤ, (k = 5 ∨ k = 3) ∧ ∃ x ∈ hexGroup (twistedX σ.toRingHom) k, x ∈ H ∧ x ≠ 1


end ExtractUNoT

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
