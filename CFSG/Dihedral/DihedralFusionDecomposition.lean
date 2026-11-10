module

public import CFSG.Dihedral.DihedralFusionStepReplacement

public noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.External BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]


theorem rightConjugate_eq_of_pointwise
    (P : Subgroup G) {a b : G}
    (hab : ∀ x ∈ P, a⁻¹ * x * a = b⁻¹ * x * b) :
    rightConjugate P a = rightConjugate P b := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, hy, by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        using (hab y hy).symm⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, hy, by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        using hab y hy⟩


end CFSG.GorensteinWalter
