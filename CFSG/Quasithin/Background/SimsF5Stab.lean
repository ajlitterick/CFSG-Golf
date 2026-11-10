module

public import CFSG.Quasithin.Background.SimsF5Form
public import CFSG.Quasithin.Background.SimsF5Klein
public import CFSG.Quasithin.Background.SimsF5Omega5

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix
open scoped Pointwise

theorem castSucc_ne_last5 (i : Fin 5) : i.castSucc ≠ Fin.last 5 := (Fin.castSucc_lt_last i).ne


@[expose] def extMat (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => ZMod 3) (if j = Fin.last 5 then 1 else 0)
      (fun i' => Fin.lastCases (motive := fun _ => ZMod 3) 0 (fun j' => A i' j') j) i

@[simp] theorem extMat_castSucc_castSucc (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) (i j : Fin 5) :
    extMat A i.castSucc j.castSucc = A i j := by
  simp only [extMat, Matrix.of_apply, Fin.lastCases_castSucc]

@[simp] theorem extMat_castSucc_last (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) (i : Fin 5) :
    extMat A i.castSucc (Fin.last 5) = 0 := by
  simp only [extMat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]

@[simp] theorem extMat_last_castSucc (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) (j : Fin 5) :
    extMat A (Fin.last 5) j.castSucc = 0 := by
  simp only [extMat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last,
    castSucc_ne_last5, if_false]

@[simp] theorem extMat_last_last (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) :
    extMat A (Fin.last 5) (Fin.last 5) = 1 := by
  simp only [extMat, Matrix.of_apply, Fin.lastCases_last, if_true]


section Reflections

open CFSG.Fischer.Classification CFSG.Fischer.Classification.F3


end Reflections


end

end CFSG.Quasithin.SimsF5
