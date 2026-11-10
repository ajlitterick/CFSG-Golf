module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineHexagonGraph
public import CFSG.GroupTheory.InvolutionHexagonMoore

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

variable {F : Type} [Field F]

@[expose] def pointGraph (F : Type) [Field F] : SimpleGraph (NonisoLine F) :=
  SimpleGraph.fromRel fun p q => ∃ T : HexLine F, p ∈ T.1 ∧ q ∈ T.1

abbrev mooreGraph (F : Type) [Field F] :
    SimpleGraph {v : NonisoLine F ⊕ HexLine F // incColoring F v = false} :=
  SimpleGraph.fromRel fun p q => ∃ ℓ : NonisoLine F ⊕ HexLine F, incColoring F ℓ = true ∧
    (incGraph F).Adj (p : NonisoLine F ⊕ HexLine F) ℓ ∧ (incGraph F).Adj (q : _) ℓ

@[expose] noncomputable def ptEquiv (F : Type) [Field F] :
    NonisoLine F ≃ {v : NonisoLine F ⊕ HexLine F // incColoring F v = false} :=
  CFSG.GroupTheory.InvolutionHexagon.ptEquiv
    (fun (p : NonisoLine F) (T : HexLine F) => p ∈ T.1)

theorem ptEquiv_apply (p : NonisoLine F) :
    ((ptEquiv F p : {v : NonisoLine F ⊕ HexLine F // incColoring F v = false}) :
      NonisoLine F ⊕ HexLine F) = Sum.inl p :=
  rfl


@[expose] noncomputable def ptIso (F : Type) [Field F] : pointGraph F ≃g mooreGraph F :=
  CFSG.GroupTheory.InvolutionHexagon.ptIso (fun (p : NonisoLine F) (T : HexLine F) => p ∈ T.1)


end CFSG.LinearGroups.UnitaryThreeOverNine
