
module

public import CFSG.GH74.KGroups.L34AutBase

public import CFSG.GH74.KGroups.L34
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.L34
public meta import CFSG.GH74.KGroups.L34AutInputs
public import Certificates.Certificate5123

public section

namespace CFSG.GH74.KGroups.L34

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix

theorem QA_valid :
    QA.check = true ∧ QA.orderCertificate = 241920 :=
  Certificates.certificate5123.1

theorem QA_ok : ValidSchreier QA := QA_valid.1

theorem orders_ok :
    orderIs PA 2 = true ∧ orderIs PB 4 = true ∧ pairInvB ws PA PB = true :=
  Certificates.certificate5123.2.1

theorem count_ok_check : pairCountB QP 2 4 ws = 241920 :=
  Certificates.certificate5123.2.2.2.2

theorem count_ok : pairCountB QP 2 4 ws = QA.orderCertificate := by
  rw [QA_valid.2]; exact count_ok_check

theorem norm_ok :
    normCheck QP QA.original.toList PA PB = true :=
  Certificates.certificate5123.2.2.1

theorem cent_ok :
    centTrivCheck (elemsT QA) PA PB = true :=
  Certificates.certificate5123.2.2.2.1

theorem autModel
    {K : Type} [Group K] (e : K ≃* QP.originalSubgroup) :
    ∃ M : AutModel K (Equiv.Perm (Fin 42)), M.P = QP.originalSubgroup ∧
      M.A = QA.originalSubgroup := by
  have ho := orders_ok
  exact autModel_exists QP QA QP_ok QA_ok PA PB QP_closure 2 4 (by norm_num) (by norm_num) ws
    ws_pos ((orderIs_iff _ (by norm_num)).1 ho.1) ((orderIs_iff _ (by norm_num)).1 ho.2.1)
    ((pairInvB_iff ws ws_pos _ _).1 ho.2.2) count_ok norm_ok cent_ok e

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

theorem finite_mulAut :
    Finite (MulAut K) := by
  obtain ⟨M, -, -⟩ := autModel e
  exact Finite.of_equiv M.A M.Φ.symm.toEquiv

theorem card_mulAut :
    Nat.card (MulAut K) = 241920 := by
  obtain ⟨M, hP, hA⟩ := autModel e
  rw [M.card_mulAut, hA, card_group QA QA_ok, QA_valid.2]


end Consequences

end CFSG.GH74.KGroups.L34
