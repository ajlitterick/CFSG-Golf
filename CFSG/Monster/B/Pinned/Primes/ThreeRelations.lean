module

public import CFSG.Monster.B.Pinned.Primes.SixPrimes
public import Certificates.Certificate16008
public import Certificates.Certificate3161

public section

namespace CFSG.Monster.B.Pinned

open Bin Primes.Native CFSG.Blueprint

theorem three_facts :
    xThree ^ 40 = 1 ∧ xThree ^ 20 ≠ 1 ∧ xThree ^ 8 ≠ 1 ∧ hThree ^ 8 = 1 ∧ hThree ^ 4 ≠ 1 ∧
      (∀ i, qThree i ^ 3 = 1 ∧ qThree i ≠ 1) ∧ zThree ^ 3 = 1 ∧ zThree ≠ 1 ∧
      (∀ i, qThree i * zThree = zThree * qThree i) ∧
      (∀ i j : Fin 8, i < j →
        bcomm (qThree i) (qThree j) = zThree ^ ((threeCommRows.getD i []).getD j 0)) ∧
      xThree⁻¹ * zThree * xThree = zThree * zThree ∧
      hThree⁻¹ * zThree * hThree = zThree * zThree ∧
      (∀ i : Fin 8, xThree⁻¹ * qThree i * xThree =
        (List.ofFn fun j => qThree j ^ (threeXRows.getD i []).getD j 0).prod *
          zThree ^ threeCVec.getD i 0) ∧
      ∀ i : Fin 8, hThree⁻¹ * qThree i * hThree =
        (List.ofFn fun j => qThree j ^ (threeYRows.getD i []).getD j 0).prod *
          zThree ^ threeDVec.getD i 0 :=
  Certificates.certificate3161


theorem orderOf_qThree
    (i : Fin 8) : orderOf (qThree i) = 3 := by
  obtain ⟨-, -, -, -, -, hq, -⟩ := three_facts
  exact orderOf_of_prime (by norm_num) (hq i)

theorem orderOf_zThree :
    orderOf zThree = 3 := by
  obtain ⟨-, -, -, -, -, -, hz3, hz1, -⟩ := three_facts
  exact orderOf_of_prime (by norm_num) ⟨hz3, hz1⟩

theorem comm_qThree_zThree
    (i : Fin 8) : qThree i * zThree = zThree * qThree i := by
  obtain ⟨-, -, -, -, -, -, -, -, hqz, -⟩ := three_facts
  exact hqz i

theorem bcomm_qThree
    (i j : Fin 8) :
    bcomm (qThree i) (qThree j) = zThree ^ (MThree i j).val := by
  obtain ⟨-, -, -, -, -, -, hz3, -, -, hc, -⟩ := three_facts
  exact bcomm_all hz3 (by exact Certificates.certificate16008.2.2.2.2.2.2.2.1)
    (by exact Certificates.certificate16008.2.2.2.2.2.2.2.2.1)
    (by exact Certificates.certificate16008.2.2.2.2.2.2.2.2.2.1) hc i j


theorem XThree_val (i j : Fin 8) :
    (XThree i j).val = (threeXRows.getD i []).getD j 0 :=
  rowsMat_val (by exact Certificates.certificate16008.2.2.2.2.2.2.2.2.2.2.1 i j)

theorem YThree_val (i j : Fin 8) :
    (YThree i j).val = (threeYRows.getD i []).getD j 0 :=
  rowsMat_val (by exact Certificates.certificate16008.2.2.2.2.2.2.2.2.2.2.2.1 i j)

theorem cThree_val (i : Fin 8) :
    (cThree i).val = threeCVec.getD i 0 := by
  rw [cThree, rowsVec, ZMod.val_natCast,
    Nat.mod_eq_of_lt (by exact Certificates.certificate16008.2.2.2.2.2.2.2.2.2.2.2.2.1 i)]

theorem dThree_val (i : Fin 8) :
    (dThree i).val = threeDVec.getD i 0 := by
  rw [dThree, rowsVec, ZMod.val_natCast,
    Nat.mod_eq_of_lt (by exact Certificates.certificate16008.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i)]

theorem conj_x_qThree
    (i : Fin 8) :
    xThree⁻¹ * qThree i * xThree =
      (List.ofFn fun j => qThree j ^ (XThree i j).val).prod * zThree ^ (cThree i).val := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := three_facts
  rw [h i]
  simp only [XThree_val, cThree_val]

theorem conj_h_qThree
    (i : Fin 8) :
    hThree⁻¹ * qThree i * hThree =
      (List.ofFn fun j => qThree j ^ (YThree i j).val).prod * zThree ^ (dThree i).val := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := three_facts
  rw [h i]
  simp only [YThree_val, dThree_val]

theorem MThree_mul_inv :
    MThree * rowsMat 3 8 threeCommInvRows = 1 :=
  Certificates.certificate16008.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem isUnit_det_MThree : IsUnit MThree.det := by
  have h := congrArg Matrix.det MThree_mul_inv
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one _ h


end CFSG.Monster.B.Pinned
