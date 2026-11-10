module

public import CFSG.Milestones.ASVolI.A3Aut.Core

public section

namespace CFSG.ASVolI

open CFSG.Open

section InnDiag


theorem burnsideAut_mul_conj_mul_inv {S : Type*} [Group S] (χ : MulAut S) (y : S) :
    χ * MulAut.conj y * χ⁻¹ = MulAut.conj (χ y) := by
  ext m
  simp [MulAut.mul_apply, map_mul, map_inv]


end InnDiag

section Transport

variable {G : Type} [Group G]


theorem burnsideAut_solvBorel_of_mulEquiv {S M : Type} [Group S] [Group M] (e : S ≃* M)
    {U : Subgroup S} (h : burnsideAut_SolvBorel M (U.map e.toMonoidHom)) :
    burnsideAut_SolvBorel S U := by
  intro Y hUY hY
  have hY' : Group.IsSolvable ↥(Y.map e.toMonoidHom) :=
    solvable_of_surjective (f := (Y.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
      (Y.equivMapOfInjective e.toMonoidHom e.injective).surjective
  have h1 := h (Y.map e.toMonoidHom) (Subgroup.map_mono hUY) hY'
  intro y hy
  have h2 : e y ∈ Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup M) : Set M) :=
    h1 ⟨y, hy, rfl⟩
  rw [← Subgroup.map_equiv_normalizer_eq] at h2
  obtain ⟨y', hy', hyy'⟩ := h2
  rwa [e.injective hyy'] at hy'

end Transport

end CFSG.ASVolI
