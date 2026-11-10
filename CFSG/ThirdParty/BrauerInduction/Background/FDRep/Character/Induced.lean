module

public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.CoindBasis
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Induced
public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Induced
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Character.Basic
public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Character.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!

# Characters of induced and coinduced representations

This file relates representation-theoretic induction and coinduction to
induction of class functions.

The main representation-theoretic calculation computes the character of a
coinduced representation as a sum over right cosets, using the explicit basis
from `FDRep.CoindBasis`. Together with the induction/coinduction isomorphism,
this proves that induction of the character of a representation agrees with
the character of the induced representation.

-/

universe u v

namespace FDRep

open CategoryTheory

section Coinduced

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

open Classical in
/--
Character formula for a coinduced representation, written as a sum over right
cosets.

The summand attached to a right coset `q` is evaluated at the chosen
representative `q.out`; it is zero unless `q.out * g * q.out⁻¹` lies in the
subgroup.
-/
lemma char_coind_over_right_cosets
    [Fintype G] (I : Subgroup G) (σ : FDRep k I) (g : G) :
    (FDRep.coind I σ).character g =
    ∑ q : Quotient (QuotientGroup.rightRel I),
      if h : q.out * g * q.out⁻¹ ∈ I
      then σ.character ⟨q.out * g * q.out⁻¹, h⟩
      else 0 := by
  let bV : Module.Basis (Fin (Module.finrank k σ)) k σ :=
    Module.finBasis k σ
  let bV' : Module.Basis (Fin (Module.finrank k σ)) k (FDRep.asRep σ) :=
    FDRep.basisAsRep σ bV
  let B := FDRep.coindBasis I σ bV
  rw [FDRep.character, LinearMap.trace_eq_matrix_trace k B, Matrix.trace]
  change (∑ p : Quotient (QuotientGroup.rightRel I) × Fin (Module.finrank k σ),
      (LinearMap.toMatrix B B ((FDRep.coind I σ).ρ g)) p p) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hmem : q.out * g * q.out⁻¹ ∈ I
  · rw [dite_eq_left hmem]
    rw [FDRep.character, LinearMap.trace_eq_matrix_trace k bV, Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.toMatrix_apply]
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    have hB : B (q, i) = FDRep.coindBasisVector I σ bV q i := by
      exact FDRep.coindBasis_apply I σ bV q i
    rw [hB]
    change bV'.repr ((FDRep.coindBasisVector I σ bV q i).val (q.out * g)) i =
      bV'.repr ((FDRep.asRep σ).ρ ⟨q.out * g * q.out⁻¹, hmem⟩ (bV' i)) i
    have hq : Quotient.mk (QuotientGroup.rightRel I) (q.out * g) = q := by
      apply Eq.trans _ (Quotient.out_eq q)
      apply Quotient.sound
      change QuotientGroup.rightRel I (q.out * g) q.out
      rw [QuotientGroup.rightRel_apply]
      have h_inv := I.inv_mem hmem
      simpa [mul_assoc] using h_inv
    rw [FDRep.coindBasisVector_val, dite_eq_left hq]
  · rw [dite_eq_right hmem]
    apply Finset.sum_eq_zero
    intro i _
    rw [LinearMap.toMatrix_apply]
    have hB : B (q, i) = FDRep.coindBasisVector I σ bV q i := by
      exact FDRep.coindBasis_apply I σ bV q i
    rw [hB]
    change bV'.repr ((FDRep.coindBasisVector I σ bV q i).val (q.out * g)) i = 0
    have hq_not : Quotient.mk (QuotientGroup.rightRel I) (q.out * g) ≠ q := by
      intro hq
      apply hmem
      have h_rel := Quotient.exact (hq.trans (Quotient.out_eq q).symm)
      change QuotientGroup.rightRel I (q.out * g) q.out at h_rel
      rw [QuotientGroup.rightRel_apply] at h_rel
      have h_inv := I.inv_mem h_rel
      simpa [mul_assoc] using h_inv
    rw [FDRep.coindBasisVector_val, dite_eq_right hq_not]
    have hzero : bV'.repr 0 = 0 := map_zero bV'.repr
    exact congrArg (fun f => f i) hzero

end Coinduced
end FDRep

namespace CFSG.ClassFun

section InducedCharacter

variable {k G : Type u}
variable [Field k] [Group G] [Finite G]

/--
Class-function induction of the character of a representation is the
character of the induced representation.
-/
@[simp]
theorem ind_ofChar
    (H : Subgroup G)
    (V : FDRep k H) :
    ClassFun.ind H (ClassFun.character V) =
      ClassFun.character (FDRep.ind H V) := by
  ext g
  rw [ClassFun.ind_apply_rightCosets]
  simp only [ClassFun.char_apply]

  have hχ :
      (FDRep.ind H V).character g =
        (FDRep.coind H V).character g :=
    congrFun (FDRep.char_eq_of_iso (FDRep.indIsoCoind H V)) g

  letI : Fintype G := Fintype.ofFinite G
  rw [hχ, FDRep.char_coind_over_right_cosets]

/--
The character of an induced representation is the induced class function
of the original character.
-/
theorem char_ind
    (H : Subgroup G)
    (V : FDRep k H) :
    ClassFun.character (FDRep.ind H V) =
      ClassFun.ind H (ClassFun.character V) :=
  (ClassFun.ind_ofChar H V).symm

end InducedCharacter

end CFSG.ClassFun


namespace FDRep


end FDRep
