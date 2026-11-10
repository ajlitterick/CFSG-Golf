module

public import CFSG.Sporadic.Recognition.McLMultiplier
public import CFSG.Sporadic.Recognition.McLMultiplierGlue
public import Certificates.Certificate6107

public section

namespace CFSG.Sporadic.Recognition.McLMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open CFSG.Sporadic.McL

theorem mclMatFacts_of_certificate :
    (∀ r ∈ mclRels, mclEvalY r = 1) ∧ (∀ i : Fin 6, mclEvalY (mclCommWord i) = mclY i) ∧
      mclEvalY mclSurjA = mA ∧ mclEvalY mclSurjB = mB :=
  Certificates.certificate6107.1

theorem mk_mclCommW_of_certificate (i : Fin 6) :
    PresentedGroup.mk (wordSet mclRels) (mclCommW i) = PresentedGroup.of i :=
  Certificates.certificate6107.2.1 i

theorem card_presentedCover_le_of_certificate :
    Finite MclCover ∧ Nat.card MclCover ≤ 2694384000 :=
  Certificates.certificate6107.2.2.1

theorem three_dvd_orderOf_mclR0_of_certificate :
    3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover) :=
  Certificates.certificate6107.2.2.2

theorem card_presentedGroup_le_of_certificate :
    Finite (PG 6 mclRels) ∧ Nat.card (PG 6 mclRels) ≤ 898128000 :=
  card_presentedGroup_le_of_cover card_presentedCover_le_of_certificate
    three_dvd_orderOf_mclR0_of_certificate mk_mclCommW_of_certificate

section Multiplier


theorem isPresentation_mclGen_of_certificate : IsPresentation mclGen (wordSet mclRels) :=
  isPresentation_mclGen_of mclMatFacts_of_certificate.1 mclMatFacts_of_certificate.2.2.1
    mclMatFacts_of_certificate.2.2.2 card_presentedCover_le_of_certificate
    three_dvd_orderOf_mclR0_of_certificate mk_mclCommW_of_certificate

theorem lift_mclCommW_of_certificate (i : Fin 6) :
    FreeGroup.lift mclGen (mclCommW i) = mclGen i :=
  lift_mclCommW_of mclMatFacts_of_certificate.1 mclMatFacts_of_certificate.2.1 i

theorem card_griessHopfMultiplier_J_of_certificate : Nat.card (griessHopfMultiplier J) = 3 :=
  card_griessHopfMultiplier_J isPresentation_mclGen_of_certificate lift_mclCommW_of_certificate
    card_presentedCover_le_of_certificate three_dvd_orderOf_mclR0_of_certificate

theorem card_griessHopfMultiplier_McL_of_certificate :
    Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.McL) = 3 :=
  card_griessHopfMultiplier_McL isPresentation_mclGen_of_certificate lift_mclCommW_of_certificate
    card_presentedCover_le_of_certificate three_dvd_orderOf_mclR0_of_certificate


theorem card_center_dvd_three_of_certificate {Q : Type} [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.McL) :
    Nat.card (Subgroup.center Q) ∣ 3 :=
  card_center_dvd_three isPresentation_mclGen_of_certificate lift_mclCommW_of_certificate
    card_presentedCover_le_of_certificate three_dvd_orderOf_mclR0_of_certificate hQ e

theorem card_ker_dvd_three_of_certificate {E : Type} [Group E] [Group.IsPerfect E]
    (q : E →* CFSG.Sporadic.McL.J) (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center E) :
    Nat.card q.ker ∣ 3 :=
  card_ker_dvd_three isPresentation_mclGen_of_certificate lift_mclCommW_of_certificate
    card_presentedCover_le_of_certificate three_dvd_orderOf_mclR0_of_certificate q hq hker


theorem exists_mulEquiv_of_triple_cover_of_certificate {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L] (q : L →* CFSG.Sporadic.McL.J) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center L) (hcard : Nat.card q.ker = 3) :
    ∃ φ : MclCover ≃* L, q.comp φ.toMonoidHom =
      coverMap isPresentation_mclGen_of_certificate lift_mclCommW_of_certificate :=
  exists_mulEquiv_of_triple_cover isPresentation_mclGen_of_certificate
    lift_mclCommW_of_certificate card_presentedCover_le_of_certificate q hq hker hcard


end Multiplier

end CFSG.Sporadic.Recognition.McLMultiplier
