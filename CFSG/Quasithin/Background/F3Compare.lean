module

public import CFSG.Quasithin.Background.F3Amalgam

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F7

universe u w w'

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w} {Y' : Type w'} [Group Y] [Group Y']
  (ι : α.Completion Y) (β : α.Completion Y') (hι : ι.IsFaithful) (hβ : β.IsFaithful)

@[expose] noncomputable def psi (uh : α.Γhat) :
    PathSet ι.graph (ι.Θ hι uh) ≃ PathSet β.graph (β.Θ hβ uh) :=
  GraphCovering.psi (ι.graphCovering hι) (β.graphCovering hβ) uh


theorem lemma_F34_3 (uh : α.Γhat) (n : ℕ)
    (htrans : ∀ p₁ p₂ : GPath ι.graph n, p₁ ∈ GPath.nbPaths ι.graph (ι.Θ hι uh) n →
      p₂ ∈ GPath.nbPaths ι.graph (ι.Θ hι uh) n →
      ∃ g : ↥(ι.φ1.range ⊔ ι.φ2.range), g • ι.Θ hι uh = ι.Θ hι uh ∧ g • p₁ = p₂)
    (p₁ p₂ : GPath β.graph n) (h₁ : p₁ ∈ GPath.nbPaths β.graph (β.Θ hβ uh) n)
    (h₂ : p₂ ∈ GPath.nbPaths β.graph (β.Θ hβ uh) n) :
    ∃ g : ↥(β.φ1.range ⊔ β.φ2.range), g • β.Θ hβ uh = β.Θ hβ uh ∧ g • p₁ = p₂ :=
  lemma_F33_4 β hβ uh n
    (fun q₁ q₂ h₁ h₂ => (ι.graphCovering hι).transitive_of_transitive' uh (ι.stabIso hι uh) n
      htrans q₁ q₂ h₁ h₂) p₁ p₂ h₁ h₂

abbrev xhat : α.Γhat := CosetGeom.γ₀ (α.Ghat1 ⊔ α.Ghat2) α.Ghat1 α.Ghat2

abbrev lhat : α.Γhat := CosetGeom.γ₁ (α.Ghat1 ⊔ α.Ghat2) α.Ghat1 α.Ghat2


end RankTwoAmalgam.Completion

end CFSG.Quasithin
