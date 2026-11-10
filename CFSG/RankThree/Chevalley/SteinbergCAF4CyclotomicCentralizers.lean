module

public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl
  CFSG.Timmesfeld.ExceptionalOrders CFSG.LieType.AlgebraicGroups


theorem natCast_zmod_ne_zero_of_pos_of_lt {p a : ℕ} (ha0 : 0 < a) (hap : a < p) :
    ((a : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd ha0 h) (by omega)


end CFSG.RankThree.Chevalley
