module

public import CFSG.LieType.AlgebraicGroups.SeminaireExp3Image

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.SeminaireExp3

open MvPolynomial TensorProduct Pointwise

section Coefficients

variable {k : Type} [Field k] (k₀ : Subfield k) {σ τ : Type}


variable {k₀}

@[expose] def coeffMap (l : k →ₗ[k₀] k₀) : MvPolynomial σ k →+ MvPolynomial σ k where
  toFun P := AddMonoidAlgebra.map (k₀.subtype.toAddMonoidHom.comp l.toAddMonoidHom) P
  map_zero' := by
    ext m
    simp
  map_add' P Q := by
    ext m
    simp

@[simp] theorem coeff_coeffMap (l : k →ₗ[k₀] k₀) (P : MvPolynomial σ k) (m : σ →₀ ℕ) :
    (coeffMap l P).coeff m = l (P.coeff m) :=
  rfl


variable (k₀) in
@[expose] def IsGeneratedOver (I : Ideal (MvPolynomial σ k)) : Prop :=
  ∃ S : Set (MvPolynomial σ k), (∀ P ∈ S, ∀ m, P.coeff m ∈ k₀) ∧ Ideal.span S = I


theorem IsGeneratedOver.sup {I J : Ideal (MvPolynomial σ k)} (hI : IsGeneratedOver k₀ I)
    (hJ : IsGeneratedOver k₀ J) : IsGeneratedOver k₀ (I ⊔ J) := by
  obtain ⟨S, hS, rfl⟩ := hI
  obtain ⟨T, hT, rfl⟩ := hJ
  exact ⟨S ∪ T, fun P hP => hP.elim (hS P) (hT P), Ideal.span_union S T⟩


end Coefficients

section Product


end Product

namespace ZariskiGL


end ZariskiGL

end CFSG.LieType.AlgebraicGroups.SeminaireExp3
