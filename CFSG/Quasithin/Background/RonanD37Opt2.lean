module

public import CFSG.Quasithin.Background.SmithD37Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.RonanD37

open CFSG.Quasithin CFSG.Quasithin.SmithD37
open scoped Matrix

section Model

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)} {F : Type} [Field F]
  (Mm : MatModel L₁ L₂ F 2)

private def uM (a : F) : Matrix (Fin 2) (Fin 2) F := !![1, a; 0, 1]


private def co (v : U) : Matrix (Fin 2) (Fin 2) F := Multiplicative.toAdd (Mm.β v)


private theorem co_injective : Function.Injective (co Mm) :=
  fun _ _ h => Mm.β.injective (Multiplicative.toAdd.injective h)


private def HasPar (g : MulAut U) (a b : F) : Prop :=
  ∀ v, co Mm (g v) = uM a * co Mm v * (uM b)ᵀ

variable {Mm}


private theorem HasPar.eq {g h : MulAut U} {a b : F} (hg : HasPar Mm g a b)
    (hh : HasPar Mm h a b) : g = h :=
  MulEquiv.ext fun v => co_injective Mm (by rw [hg v, hh v])


end Model


end CFSG.Quasithin.RonanD37
