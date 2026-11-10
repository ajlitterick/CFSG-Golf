module

public import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.GH74.QTGen4.GL4.NoNine
public import CFSG.GH74.QTGen4.U42.L28Nine
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local

public section

namespace CFSG.GH74.QTGen4.U42.VertexGen4B

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups


theorem card_psl_galois {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hodd : ¬ 2 ∣ 2 ^ n - 1 := by
    intro h
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h3 : 2 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h2 h
    have h4 : 2 ^ n - (2 ^ n - 1) = 1 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    rw [h4] at h3
    omega
  have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 2 n)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 2), hK, hgcd,
    Nat.div_one]
  simp only [Finset.Icc_self, Finset.prod_singleton]
  norm_num


end CFSG.GH74.QTGen4.U42.VertexGen4B
