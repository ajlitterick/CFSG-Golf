module

public import CFSG.Milestones.ASVolI.C61.HypBase
public import CFSG.GH74.GLS.IVK.Lifted.SL2KGroup
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Aut
public import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.Arithmetic

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped MatrixGroups


theorem burnsideC56_sl2_isSimple {K : Type} [Field K] [Fintype K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Fintype.card K = 2 ^ n) : IsSimpleGroup SL(2, K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow hK
  have h4 : 4 ≤ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : IsSimpleGroup PSL(2, K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).symm.isSimpleGroup


section Dickson


end Dickson

end CFSG.ASVolI
