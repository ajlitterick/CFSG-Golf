module

public import CFSG.ClassicalInvolution.RouteD.Perp

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti CFSG.LieType.RootSystem

section Transport

variable {ι κ : Type}

theorem LeafPairM.of_equiv (e : ι ≃ κ) {M : Matrix ι ι ℤ} {N : Matrix κ κ ℤ}
    (hMN : ∀ x y, M x y = N (e x) (e y)) {ℓ b : ι} (h : LeafPairM M ℓ b) :
    LeafPairM N (e ℓ) (e b) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun h => h1 (e.injective h), fun x hxℓ hxb => ?_, by rw [← hMN]; exact h3,
    by rw [← hMN]; exact h4⟩
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy1 : y ≠ ℓ := fun h => hxℓ (by rw [h])
  have hy2 : y ≠ b := fun h => hxb (by rw [h])
  have := h2 y hy1 hy2
  rw [hMN, hMN] at this
  exact this

theorem IsLongM.of_equiv (e : ι ≃ κ) {M : Matrix ι ι ℤ} {N : Matrix κ κ ℤ}
    (hMN : ∀ x y, M x y = N (e x) (e y)) {ℓ : ι} (h : IsLongM M ℓ) : IsLongM N (e ℓ) := by
  obtain ⟨d, hd0, hd, hmax⟩ := h
  refine ⟨fun z => d (e.symm z), fun z => hd0 _, fun z w => ?_, fun z => ?_⟩
  · have := hd (e.symm z) (e.symm w)
    rw [hMN, hMN] at this
    simpa using this
  · simpa using hmax (e.symm z)

end Transport

section Main


end Main

end CFSG.ClassicalInvolution.RouteD
