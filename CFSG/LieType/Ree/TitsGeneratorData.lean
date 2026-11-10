module

public import CFSG.LieType.Simplicity.TitsElements
public import CFSG.LieType.Ree.LargeReeRootInvolution

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Simplicity


namespace ReeTag

abbrev titsGamma :
    Subgroup (ModGL F4.tag (ZMod 2)) :=
  @reeGamma F4 (ZMod 2) _ _ (ZMod.charP 2) 0
   

variable (K : Type) [Field K]

@[expose] def titsGen0
    : ModGL F4.tag K :=
  xUnit F4.tag K (0 : Fin 4) 1 * xUnit F4.tag K (3 : Fin 4) 1

@[expose] def titsGen1
    : ModGL F4.tag K :=
  xUnit F4.tag K (2 : Fin 4) 1 * xUnit F4.tag K (1 : Fin 4) 1 *
    pinnedX F4.tag K (![0, 1, 2, 0] : Fin 4 → ℤ) 1

@[expose] def titsGen2
    : ModGL F4.tag K :=
  weylElt F4.tag K (0 : Fin 4) 1 * weylElt F4.tag K (3 : Fin 4) 1

@[expose] def titsGen3
    : ModGL F4.tag K :=
  weylElt F4.tag K (1 : Fin 4) 1 * weylElt F4.tag K (2 : Fin 4) 1 *
    weylElt F4.tag K (1 : Fin 4) 1 * weylElt F4.tag K (2 : Fin 4) 1


theorem weylElt_conj_xUnit_eq_pinnedX
    (h2 : (2 : K) = 0) :
    weylElt F4.tag K (2 : Fin 4) 1 * xUnit F4.tag K (1 : Fin 4) 1 *
        (weylElt F4.tag K (2 : Fin 4) 1)⁻¹ = pinnedX F4.tag K (![0, 1, 2, 0] : Fin 4 → ℤ) 1 := by
  have hr : reflect F4.tag (2 : Fin 4) (Pi.single (1 : Fin 4) 1) = (![0, 1, 2, 0] : Fin 4 → ℤ) := by
    funext k
    fin_cases k <;> rfl
  have h := weylElt_conj_pinnedX_of_two_eq_zero (τ := F4.tag) h2 (2 : Fin 4)
    (isRoot_single F4.tag (1 : Fin 4)) (1 : K)
  rw [← pinnedX_single F4.tag K (1 : Fin 4) (1 : K)]
  exact h.trans (congrArg (fun v => pinnedX F4.tag K v 1) hr)

theorem coe_titsG1
    (h2 : (2 : K) = 0) :
    ((titsG1 K : adjointGroup F4.tag K) : ModGL F4.tag K) = titsGen1 K := by
  rw [titsGen1, ← weylElt_conj_xUnit_eq_pinnedX K h2]
  rfl

theorem coe_titsZ1
    : ((titsZ1 K : adjointGroup F4.tag K) : ModGL F4.tag K) = titsGen2 K := by
  rw [titsZ1_eq_evalG]
  simp only [titsZ1Word, TitsBits.evalG_cons, TitsBits.evalG_nil, mul_one, Subgroup.coe_mul]
  rfl

theorem coe_titsZ2
    : ((titsZ2 K : adjointGroup F4.tag K) : ModGL F4.tag K) = titsGen3 K := by
  rw [titsZ2_eq_evalG]
  simp only [titsZ2Word, TitsBits.evalG_cons, TitsBits.evalG_nil, mul_one, Subgroup.coe_mul,
    titsGen3, mul_assoc]
  rfl


end ReeTag

end CFSG.LieType.Ree
