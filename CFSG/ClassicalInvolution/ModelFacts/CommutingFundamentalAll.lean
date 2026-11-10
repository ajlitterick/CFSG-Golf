module

public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalSymplectic
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalUnitary

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank

variable {p : ℕ} [Fact p.Prime]

@[expose] def CommutingFundamentalFactsFive (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), CFSG.ClassicalInvolution.Generic.IsFundTag t →
    StatedLieAdmissible t n p e → 5 ≤ p ^ e → CommutingFundamentalGeneration p t n e


end CFSG.ClassicalInvolution.ModelFacts
