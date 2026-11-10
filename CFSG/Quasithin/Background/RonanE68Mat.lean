module

public import CFSG.Quasithin.Background.E6EightMarkedRoots
public import CFSG.Quasithin.Background.ONanE68Sp4Roots

public section

namespace CFSG.Quasithin.RonanE68

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.Quasithin.SteinbergBS CFSG.Quasithin.E6.E68Proof.Sp4
  CFSG.Open CFSG.Quasithin.E6

variable {K : Type} [Field K] [CharP K 2]


theorem antiIdx_eq_zero_iff (a : Fin 2 ⊕ Fin 2) : (0 : Fin 4) = antiIdx a ↔ Sum.inl 0 = a := by
  rw [show (0 : Fin 4) = antiIdx (Sum.inl 0) from rfl]
  exact antiIdx.injective.eq_iff


theorem antiIdx_eq_three_iff (a : Fin 2 ⊕ Fin 2) : (3 : Fin 4) = antiIdx a ↔ Sum.inr 0 = a := by
  rw [show (3 : Fin 4) = antiIdx (Sum.inr 0) from rfl]
  exact antiIdx.injective.eq_iff

theorem longMat_eq [Finite K] (t : K) :
    (glMat (uElt (0 : K) 0 t 0 : GL (Fin 4) K)).submatrix antiIdx antiIdx =
      Matrix.of fun row col : Fin 2 ⊕ Fin 2 => (if row = col then 1 else 0) +
        (if row = Sum.inl 0 ∧ col = Sum.inr 0 then t else 0) := by
  ext a b
  simp only [Matrix.submatrix_apply, glMat_uElt_long, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Matrix.of_apply, antiIdx.injective.eq_iff, antiIdx_eq_zero_iff,
    antiIdx_eq_three_iff]
  simp only [eq_comm]


end CFSG.Quasithin.RonanE68
