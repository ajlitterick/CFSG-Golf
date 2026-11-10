module

public import CFSG.ThirdParty.BrauerInduction.Background.Rep.Invariants
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Character.Basic
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Simple

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Orthogonality of irreducible characters

This file proves the Schur orthogonality relation for characters of simple
objects of `FDRep`.

The scalar product is written algebraically as

`|G|⁻¹ * ∑ g, χ_V(g) * χ_W(g⁻¹)`,

which avoids complex conjugation and works over an algebraically closed field of
characteristic zero.
-/

open CategoryTheory CategoryTheory.Limits BigOperators

namespace FDRep

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Group G]

/--
The character scalar product computes the dimension of the equivariant Hom
space.

With the convention
`⟪χ_V, χ_W⟫ = |G|⁻¹ ∑ g, χ_V(g) * χ_W(g⁻¹)`, this scalar product is
`finrank k (W ⟶ V)`.
-/
theorem char_scalarProduct_eq_finrank_hom
    [Fintype G] [CharZero k]
    (V W : FDRep k G) :
    ((Fintype.card G : k)⁻¹) *
        (∑ g : G, V.character g * W.character g⁻¹)
      =
    (Module.finrank k (W ⟶ V) : k) := by
  have : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  let τ := Representation.linHom W.ρ V.ρ
  have hsum :
      (∑ g : G, V.character g * W.character g⁻¹) =
        ∑ g : G, τ.character g := by
    apply Finset.sum_congr rfl
    intro g _
    rw [mul_comm]
    simp only [character, Representation.char_linHom, τ]
    rfl
  rw [hsum]
  rw [Representation.average_char_eq_finrank_invariants τ]
  have hfin :
      Module.finrank k τ.invariants =
        Module.finrank k (W ⟶ V) := by
    let U : FDRep k G ⥤ Rep k G :=
      forget₂ (FDRep k G) (Rep k G)
    calc
      Module.finrank k τ.invariants
          = Module.finrank k ((U.obj W) ⟶ (U.obj V)) := by
              have h :=
                LinearEquiv.finrank_eq
                  (Rep.linHomInvariantsEquivHom (U.obj W) (U.obj V))
              have hτ :
                  Representation.linHom (U.obj W).ρ (U.obj V).ρ = τ := by
                rw [FDRep.forget₂_ρ, FDRep.forget₂_ρ]
                rfl
              rw [hτ] at h
              exact h
      _ = Module.finrank k (W ⟶ V) := by
              exact LinearEquiv.finrank_eq
                (FDRep.forget₂HomLinearEquiv W V)
  exact Nat.cast_inj.mpr hfin


end FDRep
