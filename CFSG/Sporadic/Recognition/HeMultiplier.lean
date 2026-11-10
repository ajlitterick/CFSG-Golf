module

public import CFSG.Sporadic.Recognition.HeMultiplierTables
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs

public section

namespace CFSG.Sporadic.Recognition.HeMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open CFSG.Sporadic.He Subgroup


theorem card_center_dvd_griess {S Q : Type} [Group S] [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* S) :
    Nat.card (Subgroup.center Q) ∣ Nat.card (griessHopfMultiplier S) := by
  have := hQ
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv, ← hker,
    ← hmap]
  exact Subgroup.card_map_dvd (H := CFSG.RankThree.PerfectCover.hopfMultiplier S)
    (CFSG.RankThree.PerfectCover.hopfLift q hq hker.le)


end CFSG.Sporadic.Recognition.HeMultiplier
