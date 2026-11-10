module

public import CFSG.ClassicalInvolution.RouteD.Entries

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

@[expose] def LeafPairM {ι : Type} (M : Matrix ι ι ℤ) (ℓ b : ι) : Prop :=
  ℓ ≠ b ∧ (∀ x, x ≠ ℓ → x ≠ b → M ℓ x = 0 ∧ M x ℓ = 0) ∧ M ℓ b = -1 ∧ M b ℓ = -1


@[expose] def IsLongM {ι : Type} (M : Matrix ι ι ℤ) (ℓ : ι) : Prop :=
  ∃ d : ι → ℤ, (∀ i, 0 < d i) ∧ (∀ i j, d i * M i j = d j * M j i) ∧ ∀ y, d y ≤ d ℓ


theorem LeafPairM.transpose {ι : Type} {M : Matrix ι ι ℤ} {ℓ b : ι} (h : LeafPairM M ℓ b) :
    LeafPairM M.transpose ℓ b :=
  ⟨h.1, fun x hx hb => ⟨(h.2.1 x hx hb).2, (h.2.1 x hx hb).1⟩, h.2.2.2, h.2.2.1⟩

section Families

variable {n : ℕ}


end Families


private def ent {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Fin n → Fin n → ℤ := fun i j => M i j


end CFSG.ClassicalInvolution.RouteD
