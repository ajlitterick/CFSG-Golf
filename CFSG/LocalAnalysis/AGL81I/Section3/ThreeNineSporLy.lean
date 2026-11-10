module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBigOvergroup
import Certificates.Kernel.SporSch.Ly.SepGlue
import Certificates.Kernel.Misc.E6StdSlp
import Certificates.Kernel.KDense.Y443
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.LyFive
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGTwoFive
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporInner
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporKill
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporLyLocal
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporMemoir
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOp
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporSieve
public import CFSG.GroupTheory.SylowNormalIndex
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFour
import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (oPrimeModPrimeComplement)

section Helpers

private theorem factorization_five_card_Ly {N : ℕ} (hN : N = 51765179004000000) :
    N.factorization 5 = 6 := by
  rw [hN, show 51765179004000000 = 5 ^ 6 * 3312971456256 by norm_num,
    Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

private theorem primeComplementCore_eq_bot_of_isSimpleGroup {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] {d : ℕ} (hd : d.Prime) (hdvd : d ∣ Nat.card S) :
    CFSG.RankThreeEvenClassification.Helpers.primeComplementCore S d = ⊥ := by
  obtain ⟨hN, hnd⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.primeComplementCore_properties S d hd
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · rw [h, Subgroup.card_top] at hnd
    exact absurd hdvd hnd

private theorem ly_g2_case {L : Type} [Group L] [Finite L] {Y J : Subgroup L}
    (hYJ : Y ≤ J) (hJY : J ≤ Y) (hJs : IsSimpleGroup ↥J) (h31 : 31 ∣ Nat.card Y)
    (hJmodel : CFSG.Blueprint.LieModel ↥J .G2 0 5 1) :
    CFSG.RankThreeEvenClassification.Helpers.primeComplementCore ↥Y 31 = ⊥ ∧
      ChevalleyExceptionalModel (oPrimeModPrimeComplement 31 Y) .G2 5 1 := by
  have hYeq : Y = J := le_antisymm hYJ hJY
  subst Y
  haveI : IsSimpleGroup ↥J := hJs
  have hO : CFSG.RankThreeEvenClassification.Helpers.primeComplementCore ↥J 31 = ⊥ :=
    primeComplementCore_eq_bot_of_isSimpleGroup (by norm_num) h31
  haveI : IsSimpleGroup ↥(⊤ : Subgroup ↥J) :=
    MulEquiv.isSimpleGroup Subgroup.topEquiv
  obtain ⟨e1⟩ := SporCent.nonempty_oPrimeModPrimeComplement_mulEquiv (d := 31)
    (by norm_num) (Y := J) (⊤ : Subgroup ↥J)
    (by rwa [Subgroup.card_top]) (by rw [Subgroup.index_top]; norm_num)
  have hmod : ChevalleyExceptionalModel ↥J .G2 5 1 :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hJmodel (by decide)
  exact ⟨hO, CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv
    (e1.trans Subgroup.topEquiv) hmod⟩

end Helpers

section OpBound

theorem not_pow_dvd_card_mul_card_centralizer_Ly {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .Ly) {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hd : d ≠ 31) :
    ∀ z : L, orderOf z = 5 →
      5 ^ (Nat.card L).factorization 5 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) →
      ¬ d ^ (Nat.card L).factorization d ∣ (5 ^ 3 - 1) * (5 ^ 3 - 5) * (5 ^ 3 - 5 ^ 2) *
        Nat.card (Subgroup.centralizer ({z} : Set L)) := by
  have e0 : L ≃* CFSG.Blueprint.NativeSporadic.Ly := e
  have hL : Nat.card L = 51765179004000000 :=
    (Nat.card_congr e0.toEquiv).trans CFSG.Sporadic.Ly.card_Ly
  have h5L : (Nat.card L).factorization 5 = 6 := factorization_five_card_Ly hL
  obtain ⟨-, -, -, -, hdY, -, -, -, -, -⟩ := coreOfData h
  have hdvd : d ∣ 51765179004000000 := by
    rw [← hL]
    exact hdY.trans (Subgroup.card_subgroup_dvd_card Y)
  intro z hz h56 hdiv
  have h56' : 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) := by
    rw [← h5L]
    exact h56
  rcases card_centralizer_Ly_five e hz with hC | hC
  · have hN0 : (5 ^ 3 - 1) * (5 ^ 3 - 5) * (5 ^ 3 - 5 ^ 2) *
        Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 9 * 31 := by
      rw [hC]
      norm_num
    have hdiv' : d ^ (Nat.card L).factorization d ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 9 * 31 :=
      hdiv.trans hN0
    have hmem := mem_of_prime_dvd h.d_prime
      (qs := [(2, 8), (3, 7), (5, 6), (7, 1), (11, 1), (31, 1), (37, 1), (67, 1)])
      (by norm_num) (by norm_num; exact hdvd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.d_ne_two rfl
    · exact not_pow_dvd_of_factorization (q := 3) (e := 7) (by norm_num) (Nat.card_pos.ne')
        (by rw [hL]; norm_num) (by norm_num) hdiv'
    · exact h.d_ne rfl
    · exact not_pow_dvd_of_factorization (q := 7) (e := 1) (by norm_num) (Nat.card_pos.ne')
        (by rw [hL]; norm_num) (by norm_num) hdiv'
    · exact not_pow_dvd_of_factorization (q := 11) (e := 1) (by norm_num) (Nat.card_pos.ne')
        (by rw [hL]; norm_num) (by norm_num) hdiv'
    · exact hd rfl
    · exact not_pow_dvd_of_factorization (q := 37) (e := 1) (by norm_num) (Nat.card_pos.ne')
        (by rw [hL]; norm_num) (by norm_num) hdiv'
    · exact not_pow_dvd_of_factorization (q := 67) (e := 1) (by norm_num) (Nat.card_pos.ne')
        (by rw [hL]; norm_num) (by norm_num) hdiv'
  · exact absurd (hC ▸ h56') (by norm_num)

theorem op_eq_bot_of_data_Ly {L : Type} [Group L] [Finite L] (e : L ≃* Carrier .Ly)
    {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y) :
    ∀ R : Subgroup L, IsPGroup 5 R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥ := by
  by_cases hd : d = 31
  · subst d
    have hL : Nat.card L = 51765179004000000 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ly.card_Ly
    have hdvdL : 31 ∣ Nat.card L := by
      obtain ⟨-, -, -, -, hdY, -, -, -, -, -⟩ := coreOfData h
      exact hdY.trans (Subgroup.card_subgroup_dvd_card Y)
    have he1 : 1 ≤ (Nat.card L).factorization 31 := by
      rw [← (by norm_num : Nat.Prime 31).pow_dvd_iff_le_factorization (Nat.card_pos.ne')]
      simpa using hdvdL
    have he0 : (Nat.card L).factorization 31 ≠ 0 := by omega
    refine op_eq_bot_of_data_of_inverting h ?_ ?_ (exists_inverted_thirtyOne_Ly e)
    · intro z hz h56 hdiv
      have h31 : 31 ∣ (5 ^ 2 - 1) * (5 ^ 2 - 5) *
          Nat.card (Subgroup.centralizer ({z} : Set L)) :=
        (dvd_pow_self 31 he0).trans hdiv
      rcases card_centralizer_Ly_five e hz with hC | hC <;> rw [hC] at h31 <;> norm_num at h31
    · intro v hv
      rcases card_centralizer_Ly_five e hv with hC | hC <;> rw [hC] <;> norm_num
  · exact op_eq_bot_of_data h (not_pow_dvd_card_mul_card_centralizer_Ly e h hd)

end OpBound

section Kill

private theorem ly_J_card_of_sieve {L : Type} [Group L] [Finite L] (e : L ≃* Carrier .Ly)
    {d : ℕ} {Y J : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hO5 : CFSG.Open.GLAPPrimeCoreOf 5 Y = ⊥) (hJY : J ≤ Y)
    (hJn : (J.subgroupOf Y).Normal) (hJC : Subgroup.centralizer (J : Set L) ⊓ Y = ⊥)
    (hJna : ∃ a b : ↥J, a * b ≠ b * a) (hcat : Catalog ↥J)
    (hord : Nat.card ↥J ∣ 51765179004000000) :
    Nat.card ↥J = 5859000000 ∧ CFSG.Blueprint.LieModel ↥J .G2 0 5 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨h.prime⟩
  rcases ly_sieve hcat hJna hord with ⟨h5J, -⟩ | ⟨hinn, h55⟩
  · exact (false_of_not_dvd_of_gLAPPrimeCoreOf_eq_bot Nat.prime_five hO5 hJY hJn h5J hJna).elim
  · obtain ⟨F, hFcard, hFexp⟩ := exists_exponent_five_Ly e
    obtain ⟨Q, hQY⟩ := exists_sylow_le_of_data h
    obtain ⟨g, -, hg⟩ := CFSG.RankThree.PartOne.K133H.exists_conj_le_of_sylow (Y := ⊤)
      (H := Q) le_top le_top hFexp (by rw [Subgroup.card_top, Sylow.card_eq_multiplicity,
        Nat.Prime.factorization_pow h.prime, Finsupp.single_eq_same])
    have hF'exp : ∀ x ∈ F.map (MulAut.conj g).toMonoidHom, x ^ 5 = 1 := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hFexp y hy, map_one]
    have hF'J : F.map (MulAut.conj g).toMonoidHom ≤ J := by
      rw [← Subgroup.closure_eq (F.map (MulAut.conj g).toMonoidHom)]
      exact closure_le_of_pow_eq_one hJY hJn hJC hinn
        (S := (F.map (MulAut.conj g).toMonoidHom : Set L)) (hg.trans hQY) hF'exp
    have hdvd : 5 ^ 5 ∣ Nat.card ↥J := by
      rw [← hFcard, ← Subgroup.card_map_of_injective (K := F)
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
      exact Subgroup.card_dvd_of_le hF'J
    rcases h55 hdvd with hcard | ⟨hcard, hmodel⟩
    · exfalso
      have hL : Nat.card L = 51765179004000000 :=
        (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ly.card_Ly
      have hJtop : J = ⊤ := Subgroup.eq_top_of_card_eq J (hcard.trans hL.symm)
      rw [hJtop] at hJY
      exact h.ne_top (top_le_iff.mp hJY)
    · exact ⟨hcard, hmodel⟩

private theorem ly_false_of_d_eq_seven {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .Ly) {Y J : Subgroup L} (h : SporOvergroupData L 5 7 Y)
    (hJY : J ≤ Y) (hYJ : Y ≤ J) (hJmodel : CFSG.Blueprint.LieModel ↥J .G2 0 5 1) :
    False := by
  obtain ⟨D, hDsyl, hDne, hDnorm⟩ := h.sylowD
  have hDp : IsPGroup 7 D := hDsyl.isPGroup
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hDleY : D ≤ Y := Subgroup.le_normalizer.trans (hDnorm D le_rfl hDne)
  have h7dvd : 7 ∣ Nat.card ↥D := by
    rcases hDp.card_eq_or_dvd with h1 | h
    · exact absurd (Subgroup.eq_bot_of_card_eq D h1) hDne
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 7 h7dvd
  have hxL : orderOf (x : L) = 7 := (Subgroup.orderOf_coe x).trans hx
  have hxY : (x : L) ∈ Y := hDleY x.2
  have hxne : (x : L) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxL
    norm_num at hxL
  have hFle : Subgroup.zpowers (x : L) ≤ D := Subgroup.zpowers_le.mpr x.2
  have hFne : Subgroup.zpowers (x : L) ≠ ⊥ := by
    intro hbot
    have hxbot : (x : L) ∈ (⊥ : Subgroup L) := by
      rw [← hbot]
      exact Subgroup.mem_zpowers (x : L)
    exact hxne (Subgroup.mem_bot.mp hxbot)
  have hCx : Subgroup.centralizer ({(x : L)} : Set L) ≤ Y := by
    have h1 : Subgroup.centralizer (Subgroup.zpowers (x : L) : Set L) =
        Subgroup.centralizer ({(x : L)} : Set L) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [← h1]
    exact (Subgroup.centralizer_le_normalizer _).trans (hDnorm _ hFle hFne)
  obtain ⟨t, ht2, htcomm⟩ := exists_involution_commute_seven_Ly e hxL
  have htY : t ∈ Y := hCx (Subgroup.mem_centralizer_singleton_iff.mpr htcomm)
  have hxJ : (x : L) ∈ J := hYJ hxY
  have htJ : t ∈ J := hYJ htY
  let xJ : ↥J := ⟨(x : L), hxJ⟩
  let tJ : ↥J := ⟨t, htJ⟩
  have hx7 : orderOf xJ = 7 := (Subgroup.orderOf_coe xJ).symm.trans hxL
  have ht2J : orderOf tJ = 2 := (Subgroup.orderOf_coe tJ).symm.trans ht2
  have hmem : tJ ∈ Subgroup.centralizer ({xJ} : Set ↥J) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext htcomm
  have h2 : 2 ∣ Nat.card (Subgroup.centralizer ({xJ} : Set ↥J)) := by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer ({xJ} : Set ↥J)) hmem
    rwa [ht2J] at h
  exact not_two_dvd_card_centralizer_of_lieModel_G2_five hJmodel hx7 h2

theorem ly_gTwo_of_data_of_op_eq_bot {L : Type} [Group L] [Finite L] (e : L ≃* Carrier .Ly)
    {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hOp : ∀ R : Subgroup L, IsPGroup 5 R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥) :
    d = 31 ∧ CFSG.RankThreeEvenClassification.Helpers.primeComplementCore ↥Y d = ⊥ ∧
      ChevalleyExceptionalModel (oPrimeModPrimeComplement d Y) .G2 5 1 := by
  have hO : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt 5 L :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_Ly_five L ⟨e⟩
  have hO5 : CFSG.Open.GLAPPrimeCoreOf 5 Y = ⊥ := gLAPPrimeCoreOf_eq_bot_of_data h hO
  obtain ⟨J, hJY, hJn, hJs, hJna, hJC⟩ :=
    exists_simple_normal_of_data h (by norm_num) hO5 hOp (card_center_sylow_Ly e)
  haveI : IsSimpleGroup ↥J := hJs
  have hcat : Catalog ↥J :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective h.kgroup J (MonoidHom.id ↥J)
      Function.surjective_id
  have hL : Nat.card L = 51765179004000000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ly.card_Ly
  have hord : Nat.card ↥J ∣ 51765179004000000 := by
    rw [← hL]
    exact Subgroup.card_subgroup_dvd_card J
  obtain ⟨hJcard, hJmodel⟩ :=
    ly_J_card_of_sieve e h hO5 hJY hJn hJC hJna hcat hord
  have hYJ : Y ≤ J :=
    le_of_forall_mem_inner hJY hJn hJC fun α =>
      mem_inner_of_chevalleyExceptionalModel_G2 (by norm_num) (by norm_num)
        (CFSG.Blueprint.LieModel.chevalleyExceptionalModel hJmodel (by decide)) α
  have hYcard : Nat.card Y = 5859000000 := by
    have hYeq : Y = J := le_antisymm hYJ hJY
    rw [hYeq]
    exact hJcard
  obtain ⟨-, -, -, -, hdY, hdpow, -⟩ := coreOfData h
  have hmem := mem_of_prime_dvd h.d_prime
    (qs := [(2, 6), (3, 3), (5, 6), (7, 1), (31, 1)]) (by norm_num)
    (by norm_num; rw [← hYcard]; exact hdY)
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h.d_ne_two
  · exact (not_pow_dvd_of_factorization (q := 3) (e := 7) (by norm_num) (Nat.card_pos.ne')
      (by rw [hL]; norm_num) (by rw [hYcard]; norm_num) hdpow).elim
  · exact absurd rfl h.d_ne
  · exact (ly_false_of_d_eq_seven e h hJY hYJ hJmodel).elim
  · exact ⟨rfl, ly_g2_case hYJ hJY hJs hdY hJmodel⟩

theorem ly_gTwo_of_data {L : Type} [Group L] [Finite L] (e : L ≃* Carrier .Ly)
    {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y) :
    d = 31 ∧ CFSG.RankThreeEvenClassification.Helpers.primeComplementCore ↥Y d = ⊥ ∧
      ChevalleyExceptionalModel (oPrimeModPrimeComplement d Y) .G2 5 1 := by
  exact ly_gTwo_of_data_of_op_eq_bot e h (op_eq_bot_of_data_Ly e h)

theorem sporBigLy_holds : SporBigLy := by
  intro L _ _ ⟨e⟩ d Y h
  exact ly_gTwo_of_data e h

end Kill

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
