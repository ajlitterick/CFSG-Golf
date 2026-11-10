module

public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Monster.CodeAut.Perm
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.Monster.Code.Weights

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code

abbrev P24 : Type := Equiv.Perm (Fin 24)


@[expose] def MY {α : Type*} [MulAction P24 α] (Γ : Subgroup P24) (Y : α) : Subgroup P24 :=
  Γ ⊓ MulAction.stabilizer P24 Y

@[expose] def KY {α : Type*} [MulAction P24 α] (Γ : Subgroup P24) (Y : α) : Subgroup P24 :=
  pCoreOf 2 (MY Γ Y)


@[expose] def natHom (d : ℕ) (K : Type*) [Field K] :
    GL (Fin d) K →* MulAut (Multiplicative (Fin d → K)) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd
        ((g : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v))
      invFun := fun v => Multiplicative.ofAdd
        (((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v))
      left_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      right_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      map_mul' := fun v w => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_add] }
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp [Matrix.mulVec_mulVec]


end CFSG.Quasithin.RonanH143
