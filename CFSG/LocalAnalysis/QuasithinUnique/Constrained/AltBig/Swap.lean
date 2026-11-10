module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Basic
public import CFSG.Quasithin.Background.B1More13A

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup CFSG.Open
open scoped commutatorElement

section TC

variable {β : Type} [Fintype β] [DecidableEq β]


def altOn (C : Finset β) : Subgroup (Perm β) :=
  alternatingGroup β ⊓ fixOn ((C : Set β)ᶜ)


theorem ftc7_perm_pair {p q : β} (hpq : p ≠ q) {σ : Perm β} (hp : σ p = p ∨ σ p = q)
    (hq : σ q = p ∨ σ q = q) : (σ p = p ∧ σ q = q) ∨ (σ p = q ∧ σ q = p) := by
  rcases hp with h1 | h1 <;> rcases hq with h2 | h2
  · exact absurd (σ.injective (h1.trans h2.symm)) hpq
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (σ.injective (h1.trans h2.symm)) hpq


end TC

end CFSG.QuasithinUnique.L246C127.AltBig
