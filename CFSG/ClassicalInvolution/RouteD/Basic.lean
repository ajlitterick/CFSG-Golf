module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

variable {B : Type} [Fintype B]

@[expose] def stdCartan (t : DynkinType) : Matrix (Fin t.rank) (Fin t.rank) ℤ :=
  t.cartanMatrix.transpose

theorem stdCartan_apply (t : DynkinType) (i j : Fin t.rank) :
    stdCartan t i j = t.cartanMatrix j i := rfl

omit [Fintype B] in
theorem diagramGraph_transpose (A : Matrix B B ℤ) :
    diagramGraph A.transpose = diagramGraph A := by
  ext i j
  simp only [diagramGraph_adj, Matrix.transpose_apply]
  tauto

theorem classify {Γ : Matrix B B ℤ} (h : IsFiniteType Γ) (hc : (diagramGraph Γ).Connected) :
    ∃ t : DynkinType, t.Valid ∧ ∃ e : B ≃ Fin t.rank, ∀ x y, Γ x y = stdCartan t (e x) (e y) := by
  have hc' : (diagramGraph Γ.transpose).Connected := by rwa [diagramGraph_transpose]
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ := h.transpose.existsUnique_dynkinType hc'
  exact ⟨t, ht, e, fun x y => by simpa [stdCartan_apply] using he y x⟩


end CFSG.ClassicalInvolution.RouteD
