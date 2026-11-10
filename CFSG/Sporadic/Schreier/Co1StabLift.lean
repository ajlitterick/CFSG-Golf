module

public import CFSG.Sporadic.Schreier.Co1QuotCheck
public import CFSG.Sporadic.Schreier.Co1Lift
public import CFSG.Sporadic.SuzOddCore.LiftedValid
public import CFSG.Sporadic.Co2

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD toVecD_xor toVecD_injective rowsMatrix)
open CFSG.Sporadic.SmallF2.Native Matrix CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2
  CFSG.Certificates

@[expose] noncomputable def quotRep (k : ℕ) : Vec24 := toVecD 24 Data.liftReps.toArray[k]!


@[expose] noncomputable def stabG0 : stabH := ⟨stabH0, stabH0_mem⟩

@[expose] noncomputable def stabG1 : stabH := ⟨stabH1, stabH1_mem⟩

@[expose] noncomputable def stabU :
    Vector stabH co2Q.originalCount :=
  ⟨#[stabG0, stabG1], by rw [co2Q_originalCount]; rfl⟩

@[expose] noncomputable def stabW : GL24 := stabH0⁻¹ * stabH1 * stabH1 * stabH0 * stabH1 * stabH0⁻¹

theorem quot_facts : Data.quotAct0.toArray = co2OrigArrs[0]! ∧
    Data.quotAct1.toArray = co2OrigArrs[1]! ∧ Native.hRows0 = Data.subRows0.toArray ∧
    Native.hRows1 = Data.subRows1.toArray := by
  have h := quot_check
  simp only [Native.quotCheck, Native.quotCheckOf, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩


theorem clsHom_stabG0 :
    clsHom stabG0 = co2Gen 0 := clsHom_gen0

theorem clsHom_stabG1 :
    clsHom stabG1 = co2Gen 1 := clsHom_gen1


theorem clsHom_injective :
    Function.Injective clsHom := fun g g' h =>
  stabPermEquiv.injective (Subtype.ext (show (stabPermEquiv g : Equiv.Perm (Fin 2300)) =
    stabPermEquiv g' by rw [stabPermEquiv_apply, stabPermEquiv_apply]; exact h))


theorem isSimpleGroup_stabH :
    IsSimpleGroup stabH :=
  @MulEquiv.isSimpleGroup (↥stabH) (Subgroup.toGroup stabH) Blueprint.NativeSporadic.Co2
    Units.instGroup CFSG.Sporadic.Co2.isSimpleGroup_Co2 stabCo2Equiv

@[expose] noncomputable def stabWS : stabH :=
  stabG0⁻¹ * stabG1 * stabG1 * stabG0 * stabG1 * stabG0⁻¹

@[expose] noncomputable def stabTS : stabH := stabG0 * stabWS⁻¹ * stabG1 * stabWS

theorem coe_stabG0 : (stabG0 : GL24) = stabH0 := by
  rw [show stabG0 = ⟨stabH0, stabH0_mem⟩ from rfl]

theorem coe_stabG1 : (stabG1 : GL24) = stabH1 := by
  rw [show stabG1 = ⟨stabH1, stabH1_mem⟩ from rfl]

theorem coe_stabTS : (stabTS : GL24) = stabH0 * stabW⁻¹ * stabH1 * stabW := by
  rw [stabTS, stabWS, stabW]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_stabG0, coe_stabG1]

theorem orderOf_stabT :
    orderOf (stabH0 * stabW⁻¹ * stabH1 * stabW) = 23 := by
  have hw : clsHom stabWS = co2W := by
    rw [co2W_eq, stabWS]
    simp only [map_mul, map_inv, clsHom_stabG0, clsHom_stabG1]
  have himg : clsHom stabTS = co2cGen 0 * co2cGen 1 := by
    rw [co2cGen_zero, co2cGen_one, stabTS]
    simp only [map_mul, map_inv, clsHom_stabG0, clsHom_stabG1, hw, mul_assoc]
  rw [← coe_stabTS, Subgroup.orderOf_coe, ← orderOf_injective clsHom clsHom_injective stabTS,
    himg, orderOf_co2cGen_mul]


end CFSG.Sporadic.Co1Schreier
