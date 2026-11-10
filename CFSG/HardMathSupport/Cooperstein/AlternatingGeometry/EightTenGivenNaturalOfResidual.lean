module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenResidualR1

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open


@[expose] def EightTenResidualOutcomes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → ∀ m : ℕ, 8 < m →
    ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m) →
    NaturalSectionLSL S L m → EightTenResidual' S L m → EightTenOutcomes X S L

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
