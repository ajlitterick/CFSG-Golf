module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutData
public import CFSG.Quasithin.MS93.S46KC2Fin
public import CFSG.Quasithin.MS93.S46Stmt
public import CFSG.Quasithin.MS93.S46X3Lin
public import CFSG.Quasithin.MS93.S4AH1

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.X3 CFSG.Quasithin.MS93.S46.KC2
open scoped commutatorElement Matrix

namespace KCF

section Grp

variable {𝔾 : Type} [Group 𝔾] {F : Type}

@[expose] def zprod (w : Fin 6 → F → 𝔾) (s : Fin 6 → F) (L : List (Fin 6)) : 𝔾 :=
  (L.map fun i => w i (s i)).prod

theorem zprod_nil (w : Fin 6 → F → 𝔾) (s : Fin 6 → F) : zprod w s [] = 1 := rfl

theorem zprod_cons (w : Fin 6 → F → 𝔾) (s : Fin 6 → F) (i : Fin 6) (L : List (Fin 6)) :
    zprod w s (i :: L) = w i (s i) * zprod w s L := rfl

theorem zprod_mem {H : Subgroup 𝔾} {w : Fin 6 → F → 𝔾} (hw : ∀ i s, w i s ∈ H)
    (s : Fin 6 → F) (L : List (Fin 6)) : zprod w s L ∈ H := by
  induction L with
  | nil => exact H.one_mem
  | cons i L ih =>
    rw [zprod_cons]
    exact H.mul_mem (hw i (s i)) ih

end Grp


end KCF

end CFSG.Quasithin.MS93.S46
