module

public import CFSG.LieType.Chevalley.C2E6MinusSixBase
public import CFSG.LieType.Chevalley.C2E6MinusSixWitt

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem map_symm_map (φ : QuadraticMap.IsometryEquiv Q Q) (V : Submodule (ZMod 2) X) :
    (V.map (φ.toLinearEquiv : X →ₗ[ZMod 2] X)).map (φ.symm.toLinearEquiv : X →ₗ[ZMod 2] X) = V := by
  have h := mapVertex_mapVertex (g := φ) (h := φ.symm) φ.symm_apply_apply
  ext v
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    have : (φ.symm.toLinearEquiv : X →ₗ[ZMod 2] X) ((φ.toLinearEquiv : X →ₗ[ZMod 2] X) u) = u :=
      φ.symm_apply_apply u
    rw [this]
    exact hu
  · intro hv
    exact ⟨φ v, ⟨v, hv, rfl⟩, φ.symm_apply_apply v⟩


end CFSG.LieType.Chevalley.C2E6Overlap
