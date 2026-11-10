module

public import CFSG.ThirdParty.BrauerInduction.Background.LinearChar.Basic
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.InducedFinrank

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Induced representations attached to linear characters

This file defines induction and coinduction of the one-dimensional
representation associated to a linear character.

Character formulas are kept in `LinearChar.InducedCharacter`.
-/

universe u v

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

namespace FDRep

open Module

/--
Induced Linear Representation: `Ind_H^G(ψ)`.
This is the atomic basis for Brauer's theorem.
-/
@[expose] noncomputable def indLin (H : Subgroup G)
    (ψ : H →* kˣ) : FDRep k G :=
  FDRep.ind H (FDRep.ofLinearChar ψ)

/-- `Coind_H^G(ψ)` as an `FDRep`. -/
@[expose] noncomputable def coindLin (H : Subgroup G)
    (ψ : H →* kˣ) : FDRep k G :=
  FDRep.coind H (FDRep.ofLinearChar ψ)

@[simp]
lemma coindLin_ρ_apply (H : Subgroup G) (ψ : H →* kˣ)
    (g : G) (v : (FDRep.coindLin H ψ)) (x : G) :
    ((FDRep.coindLin H ψ).ρ g v).1 x = v.1 (x * g) := rfl


/--
The dimension of a representation induced from a linear character, expressed
using the right-coset quotient.
-/
@[simp]
theorem finrank_indLin_rightRel
    {k : Type u} [Field k]
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (ψ : H →* kˣ) :
    (FDRep.indLin H ψ).finrank =
      Nat.card (Quotient (QuotientGroup.rightRel H)) := by
  classical
  dsimp [FDRep.indLin]
  rw [FDRep.finrank_ind_rightRel]
  simp only [finrank_ofLinearChar, mul_one]

end FDRep
