module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Defs
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Adapters.StatedPSLTwoNine
import CFSG.LieType.SeitzGeneration.UnitaryHyperDiag
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.QTK.Section
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.Foundations
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
import CFSG.LieType.SeitzGeneration.UnitaryBlocks
import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup CFSG.Open


theorem small_pRank_top_le_two_of_not_dvd {S : Type} [Group S] [Finite S] {r : ℕ} (hr : r.Prime)
    (h : ¬ r ^ 3 ∣ Nat.card S) : CFSG.Open.pRank r (⊤ : Subgroup S) ≤ 2 := by
  refine CFSG.SectionRank.pRank_le hr.one_lt fun E _ hE => ?_
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.card E = r ^ k :=
    IsPGroup.iff_card.1 fun g => ⟨1, Subtype.ext (by
      rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hE.2 _ g.2)⟩
  rw [hk]
  by_contra hlt
  push Not at hlt
  have h3 : r ^ 3 ∣ r ^ k := Nat.pow_dvd_pow r (by
    by_contra h'
    push Not at h'
    have : r ^ k ≤ r ^ 2 := Nat.pow_le_pow_right hr.pos (by omega)
    omega)
  exact h (h3.trans (hk ▸ Subgroup.card_subgroup_dvd_card E))


section ThreeRank

open CFSG.SectionRank.OddCover Matrix

theorem small_card_scalars_statedSL_three {K : Type} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) :
    Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) = 3 := by
  set D := (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)
  have hdvd : Nat.card D ∣ 3 := card_scalars_dvd (by norm_num) _ fun x c hc => by
    have hdet := det_of_mem_statedSL x.1.2
    rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [card_units_eq]; exact h3)
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hcS : (GeneralLinearGroup.scalar (Fin 3) c) ∈ StatedSL 3 K := by
    refine Subgroup.subset_closure ?_
    change ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Units.val_pow_eq_pow_val, hc3,
      Units.val_one]
  have hx : (⟨GeneralLinearGroup.scalar (Fin 3) c, hcS⟩ : StatedSL 3 K) ∈ D :=
    Subgroup.mem_subgroupOf.2 ⟨c, rfl⟩
  have hne : D ≠ ⊥ := by
    intro hbot
    have h1 := (Subgroup.mem_bot.1 (hbot ▸ hx))
    have h2 := scalar_injective (K := K) (n := 3) (by norm_num)
      (congrArg (fun g : StatedSL 3 K => (g : GL (Fin 3) K)) h1 |>.trans (map_one _).symm)
    rw [h2, orderOf_one] at hc
    omega
  have hcard : Nat.card D ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq D h)
  exact (Nat.dvd_prime Nat.prime_three).1 hdvd |>.resolve_left hcard

theorem small_pRank_three_statedSL_le_two {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (h3 : 3 ∣ p ^ f - 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 3 K))) ≤ 2 := by
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hq2 : 2 ≤ p ^ f :=
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact (not_three_dvd_pow_add_sub hf).2 h3
  refine three_pRank_statedProj_le_two monomialData_statedSL ?_
    (small_card_scalars_statedSL_three (by rwa [hK]))
  have hM : Nat.card (⊤ : Subgroup Kˣ) = p ^ f - 1 := by
    rw [Subgroup.card_top, card_units_eq, hK]
  rw [card_statedSL_three, hK, hM, ← factorization_six_mul_three (by
    have : 0 < p ^ f - 1 := by omega
    positivity)]
  have e1 : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
    zify [hq1, Nat.one_le_pow 2 _ hq1]; ring
  have e2 : (p ^ f) ^ 3 - 1 = (p ^ f - 1) * ((p ^ f) ^ 2 + p ^ f + 1) := by
    zify [hq1, Nat.one_le_pow 3 _ hq1]; ring
  rw [e1, e2]
  exact factorization_order_eq Nat.prime_three (by norm_num) (by positivity) (by omega)
    (by omega) (by positivity)
    (fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm)
    (by omega) (factorization_sq_add_add_one Nat.prime_three hq1 h3)

end ThreeRank


section Sporadic

open CFSG.Blueprint


end Sporadic

end CFSG.SectionRank.QTK.CentreFact
