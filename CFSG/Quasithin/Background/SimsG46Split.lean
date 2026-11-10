module

public import CFSG.Quasithin.Background.SimsG4Core
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import CFSG.Quasithin.Background.SimsG45Transv

public section

namespace CFSG.Quasithin.SimsG4

namespace G46Case3

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

section Basic

variable (B : LinearMap.BilinForm F V)


end Basic

section Transv

variable {B : LinearMap.BilinForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)}


end Transv

section Split

variable {B : LinearMap.BilinForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)}

structure IsSplit (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V))
    (V₁ V₂ : Submodule F V) : Prop where
  line₁ : IsNondegLine B V₁
  line₂ : IsNondegLine B V₂
  orth₁ : B.orthogonal V₁ = V₂
  orth₂ : B.orthogonal V₂ = V₁
  compl : IsCompl V₁ V₂
  cover : ∀ d ∈ transvSet G₀, commSpace d ≤ V₁ ∨ commSpace d ≤ V₂
  pair₁ : ∃ a ∈ transvSet G₀, ∃ b ∈ transvSet G₀,
    commSpace a ≤ V₁ ∧ commSpace b ≤ V₁ ∧ a * b ≠ b * a
  pair₂ : ∃ a ∈ transvSet G₀, ∃ b ∈ transvSet G₀,
    commSpace a ≤ V₂ ∧ commSpace b ≤ V₂ ∧ a * b ≠ b * a

theorem IsSplit.symm {V₁ V₂ : Submodule F V} (h : IsSplit B G₀ V₁ V₂) : IsSplit B G₀ V₂ V₁ :=
  ⟨h.line₂, h.line₁, h.orth₂, h.orth₁, h.compl.symm, fun d hd => (h.cover d hd).symm,
    h.pair₂, h.pair₁⟩


end Split

end G46Case3

end CFSG.Quasithin.SimsG4
