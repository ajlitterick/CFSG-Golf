module

public import CFSG.Quasithin.Background.G13Theta
public import CFSG.Quasithin.Background.G13Fam
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.G13Two

public section

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin.G1


section natural

variable {F : Type} [Field F] {n : ℕ} {U : Type} [AddCommGroup U]
  [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]


end natural


end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Quasithin.G1 CFSG.ASVolI.ChG


section G14

variable {F : Type} [Field F] {n : ℕ}


end G14


section G15Help

open CFSG.Quasithin.SL2Model

variable {F : Type} [Field F]


end G15Help


section G15Four

variable {F : Type} [Field F]


end G15Four


section G16

open CFSG.Quasithin.SL2Model

variable {F : Type} [Field F]


private def g16qAct {V : Type} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) →+
      (V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) :=
  QuotientAddGroup.map _ _ (actU g) fun c hc k _ => by
    show k • g • c = g • c
    calc k • g • c = (k * g) • c := (mul_smul k g c).symm
      _ = (g * (g⁻¹ * k * g)) • c := by congr 1; group
      _ = g • ((g⁻¹ * k * g) • c) := mul_smul _ _ _
      _ = g • c := by rw [hc (g⁻¹ * k * g) (Subgroup.mem_top _)]

private instance g16Quot {V : Type} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V] :
    DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F)
      (V ⧸ fixU (U := V) (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) where
  smul g q := g16qAct g q
  one_smul q := by
    refine QuotientAddGroup.induction_on q fun v => ?_
    exact congrArg QuotientAddGroup.mk (one_smul _ v)
  mul_smul g h q := by
    refine QuotientAddGroup.induction_on q fun v => ?_
    exact congrArg QuotientAddGroup.mk (mul_smul g h v)
  smul_zero g := map_zero (g16qAct g)
  smul_add g q r := map_add (g16qAct g) q r


private def g16Tw (g : Matrix.SpecialLinearGroup (Fin 2) F) (V : Type) : Type := V

private instance g16TwAddCommGroup (g : Matrix.SpecialLinearGroup (Fin 2) F) (V : Type)
    [AddCommGroup V] : AddCommGroup (g16Tw g V) :=
  inferInstanceAs (AddCommGroup V)

private instance g16TwDMA (g : Matrix.SpecialLinearGroup (Fin 2) F) (V : Type)
    [AddCommGroup V] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) V] :
    DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) (g16Tw g V) where
  smul k v := ((g * k * g⁻¹) • (show V from v) : V)
  one_smul v := by
    show (g * 1 * g⁻¹) • (show V from v) = show V from v
    rw [mul_one, mul_inv_cancel, one_smul]
  mul_smul k l v := by
    show (g * (k * l) * g⁻¹) • (show V from v) =
      (g * k * g⁻¹) • ((g * l * g⁻¹) • (show V from v))
    rw [← mul_smul, show g * k * g⁻¹ * (g * l * g⁻¹) = g * (k * l) * g⁻¹ by group]
  smul_zero k := by
    show (g * k * g⁻¹) • (0 : V) = 0
    exact smul_zero _
  smul_add k v w := by
    show (g * k * g⁻¹) • ((show V from v) + (show V from w)) =
      (g * k * g⁻¹) • (show V from v) + (g * k * g⁻¹) • (show V from w)
    exact smul_add _ _ _

private instance g16TwFinite (g : Matrix.SpecialLinearGroup (Fin 2) F) (V : Type)
    [AddCommGroup V] [Finite V] : Finite (g16Tw g V) :=
  inferInstanceAs (Finite V)

end G16

section G16Thm

open CFSG.Quasithin.SL2Model


end G16Thm


end CFSG.ASVolI
