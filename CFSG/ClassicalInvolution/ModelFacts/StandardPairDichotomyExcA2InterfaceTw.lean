module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Interface
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2TwPair

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

@[expose] def A2UnitaryTw (p e : ℕ) [Fact p.Prime] : Prop :=
  StatedLieAdmissible .twistedE6 0 p e → p ≠ 2 → 5 ≤ p ^ e →
    ∀ (R₂ : Subgroup (twistedE6Group p e)) (c₂ : twistedE6Group p e),
      R₂ ∈ longestFundamental (twistedE6Datum p e) → c₂ ∈ R₂ → orderOf c₂ = 2 →
      LeviE6.phiE6 p e c₂ * signDiagE6 (LeviE6.E6Closure p e) thetaE6 =
        signDiagE6 (LeviE6.E6Closure p e) thetaE6 * LeviE6.phiE6 p e c₂ →
      ¬ (∀ r ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6), c₂ * r = r * c₂) →
      (∃ v ∈ h1E6 (LeviE6.E6Closure p e),
        v * LeviE6.phiE6 p e c₂ * v⁻¹ = signDiagE6 (LeviE6.E6Closure p e) deltaE6 ∧
        ∃ m ∈ parabolicLevi .E6 (LeviE6.E6Closure p e) JE6,
          LeviE6.frobE6 p e v * v⁻¹ = m * rootSL2 .E6 (LeviE6.E6Closure p e) thetaE6 WSL) →
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
        (stdRankOne (twistedE6Datum p e) (proj thetaE6)) R₂

end CFSG.ClassicalInvolution.ModelFacts.Levi
