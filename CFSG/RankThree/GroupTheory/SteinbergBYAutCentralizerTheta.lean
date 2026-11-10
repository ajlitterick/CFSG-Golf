module

public import CFSG.RankThree.GroupTheory.SteinbergCECentralThetaQuasisimple

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank

theorem map_inSubgroup_aschbacherSolvableCore_mulEquiv {G G' : Type*} [Group G] [Group G']
    [Finite G] {p : ℕ} (hp : p.Prime) (φ : G ≃* G') (X : Subgroup G) :
    (inSubgroup (aschbacherSolvableCore p) X).map φ.toMonoidHom =
      inSubgroup (aschbacherSolvableCore p) (X.map φ.toMonoidHom) := by
  rw [inSubgroup, inSubgroup,
    ← aschbacherSolvableCore_map_mulEquiv hp (X.equivMapOfInjective φ.toMonoidHom φ.injective),
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem mulAut_conj_apply_eq {C : Type*} [Group C] (β : MulAut C) (d : C) :
    MulAut.conj (β d) = β * MulAut.conj d * β⁻¹ := by
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]


end CFSG.RankThree.GroupTheory.SteinbergBY
