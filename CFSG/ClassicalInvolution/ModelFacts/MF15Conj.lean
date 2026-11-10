module

public import CFSG.ClassicalInvolution.ModelFacts.MF15One
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutWitt

public section

namespace CFSG.ClassicalInvolution.ModelFacts.MF15

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.ModelFacts.OrthAut
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}


theorem frame_map_eq_of_apply (fr fr' : Frame Q) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h1 : g fr.e₁ = fr'.e₁)
    (h2 : g fr.f₁ = fr'.f₁) (h3 : g fr.e₂ = fr'.e₂) (h4 : g fr.f₂ = fr'.f₂) :
    fr.map hg = fr' := by
  obtain ⟨⟨e₁, f₁, a₁, b₁, c₁⟩, ⟨e₂, f₂, a₂, b₂, c₂⟩, o⟩ := fr
  obtain ⟨⟨e₁', f₁', a₁', b₁', c₁'⟩, ⟨e₂', f₂', a₂', b₂', c₂'⟩, o'⟩ := fr'
  simp only [Frame.map, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂] at h1 h2 h3 h4 ⊢
  subst h1 h2 h3 h4
  rfl


end CFSG.ClassicalInvolution.ModelFacts.MF15
