module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2All
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyE6
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyE7
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryE8Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryMain
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryTwMain

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.ModelFacts.Levi

theorem standardPairDichotomyFE_proved {p : ℕ} [Fact p.Prime] : StandardPairDichotomyFE p :=
  standardPairDichotomyFE_of_unitary (fun _ => a2UnitaryF4) (fun _ => a2UnitaryE6)
    (fun _ => a2UnitaryE7) (fun _ => a2UnitaryE8) (fun _ => a2UnitaryTw)

end CFSG.ClassicalInvolution.ModelFacts
