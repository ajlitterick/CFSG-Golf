module

public import CFSG.Quasithin.Background.RonanH49Base
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr
open scoped Matrix

open CFSG.LieType.SteinbergBR.AutGL32 in
@[expose] noncomputable def iotaSL : ↥SL32 →* ↥SL32 where
  toFun a := ⟨tau (a : GL (Fin 3) (ZMod 2)), mem_SL32 _⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

theorem mat_iotaSL (a : ↥SL32) : mat (iotaSL a) = (mat a⁻¹)ᵀ := by
  change ((CFSG.LieType.SteinbergBR.AutGL32.tau (a : GL (Fin 3) (ZMod 2)) :
    GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
  rw [CFSG.LieType.SteinbergBR.AutGL32.tau_val]
  rfl

@[expose] noncomputable def rhoT : ↥SL32 →* MulAut WMod :=
  rho.comp ((MonoidHom.id _).prod iotaSL)

theorem rhoT_apply (a : ↥SL32) : rhoT a = rho (a, iotaSL a) := rfl

theorem toAdd_rhoT (a : ↥SL32) (X : WMod) :
    Multiplicative.toAdd (rhoT a X) = mat a * Multiplicative.toAdd X * mat a⁻¹ := by
  rw [rhoT_apply, toAdd_rho]
  simp only [mat_iotaSL, Matrix.transpose_transpose]

theorem rhoT_injective : Function.Injective rhoT := by
  intro a b h
  have := rho_injective h
  exact (Prod.mk.inj this).1

theorem toAdd_dWd : Multiplicative.toAdd dWd = 1 := by
  decide


theorem rhoT_mem_Cd (a : ↥SL32) : rhoT a ∈ Cd := by
  rw [mem_Cd]
  refine ⟨img_le_norm (rho_mem_img _), ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_rhoT, toAdd_dWd, Matrix.mul_one, ← mat_mul, mul_inv_cancel, mat_one]


theorem rhoT_range_le_Cd : rhoT.range ≤ Cd := by
  rintro _ ⟨a, rfl⟩
  exact rhoT_mem_Cd a

noncomputable abbrev Kc : Subgroup ↥Cd := rhoT.range.subgroupOf Cd


noncomputable def eK : ↥Kc ≃* ↥SL32 :=
  (Subgroup.subgroupOfEquivOfLe rhoT_range_le_Cd).trans (MonoidHom.ofInjective rhoT_injective).symm


end CFSG.Quasithin.RonanH49
