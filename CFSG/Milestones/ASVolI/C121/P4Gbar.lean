module

public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.Quasithin.Background.C1PackSL2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem burnsideC121_p4_psl_equiv {G : Type} [Group G] {n : ℕ} (h : IsPSL 2 2 n G) :
    2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Fintype K), Fintype.card K = 2 ^ n ∧
      Nonempty (G ≃* SL(2, K)) := by
  obtain ⟨hadm, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  obtain ⟨-, hn1, -, hne, -⟩ := hadm
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn : n = 1 := by omega
    subst hn
    exact hne rfl
  let _ : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hcard]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow hc
  exact ⟨hn2, K, hK, inferInstance, hc,
    ⟨e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq B42L2.center_sl2_eq_bot).trans
        QuotientGroup.quotientBot))⟩⟩


end CFSG.Quasithin
