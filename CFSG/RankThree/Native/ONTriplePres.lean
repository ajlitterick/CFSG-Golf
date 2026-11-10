module

public import CFSG.Certificates.CosetTableCompactColumns
public meta import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.RankThree.Native.ONTriplePresInputs
public import Certificates.Certificate8144

public section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.CosetTable

abbrev FHat (e₁ e₂ e₃ : ℕ) : Type := PG 8 (coverRels e₁ e₂ e₃)

theorem card_coxeter_le :
    Finite (PG (subsetOf 8 [0, 1, 2, 3, 4, 5]).length C1) ∧
    Nat.card (PG (subsetOf 8 [0, 1, 2, 3, 4, 5]).length C1) ≤ 3753792 :=
  Certificates.certificate8144.1


theorem card_FHat_one_le :
    Finite (FHat 1 1 1) ∧ Nat.card (FHat 1 1 1) ≤ 1382446517760 :=
  Certificates.certificate8144.2.1

theorem card_FHat_zero_le :
    Finite (FHat 0 0 0) ∧ Nat.card (FHat 0 0 0) ≤ 1382446517760 :=
  Certificates.certificate8144.2.2.1

theorem index_FHat_one_le :
    (genSub {r : FreeGroup (Fin 8) | r ∈ (coverRels 1 1 1).map FreeGroup.mk}
      (subsetOf 8 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 8) | r ∈ (coverRels 1 1 1).map FreeGroup.mk}
      (subsetOf 8 [0, 1, 2, 3, 4, 5])).index ≤ 368280 :=
  Certificates.certificate8144.2.2.2

end CFSG.RankThree.Native.ONTriple
