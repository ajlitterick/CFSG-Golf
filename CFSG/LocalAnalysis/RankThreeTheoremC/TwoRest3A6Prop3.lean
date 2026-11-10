module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3A6CubeN
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Out
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexOrbit
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_ne_one_of_card_center_eq_three {Q : Type*} [Group Q]
    (hZ : Nat.card (Subgroup.center Q) = 3) :
    ∃ ζ ∈ Subgroup.center Q, ζ ≠ 1 ∧ orderOf ζ ∣ 3 := by
  have hne : Subgroup.center Q ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hZ; omega
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨x, x.2, fun h => hx (Subtype.ext h), ?_⟩
  have := Subgroup.orderOf_dvd_natCard (Subgroup.center Q) x.2
  rwa [hZ] at this

theorem false_of_card_center_eq_three_of_alt {Q : Type*} [Group Q]
    (hZ : Nat.card (Subgroup.center Q) = 3) {m : ℕ} (hm : m ≠ 3)
    (e : Q ≃* alternatingGroup (Fin m)) : False := by
  obtain ⟨ζ, hζ, hζ1, -⟩ := exists_ne_one_of_card_center_eq_three hZ
  apply hζ1
  rw [← e.map_eq_one_iff]
  rcases Nat.lt_or_ge m 3 with h | h
  · have hbot := alternatingGroup.eq_bot_of_card_le_two (α := Fin m) (by simp; omega)
    exact Subtype.ext (Subgroup.mem_bot.mp (hbot.le (e ζ).2))
  · have hcen : e ζ ∈ Subgroup.center (alternatingGroup (Fin m)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨q, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hζ q)]
    rw [alternatingGroup.center_eq_bot (by simp; omega)] at hcen
    exact Subgroup.mem_bot.mp hcen

theorem eq_three_of_card_alternatingGroup {n : ℕ}
    (h : Nat.card (alternatingGroup (Fin (2 * n))) = 360) : n = 3 := by
  rcases n with _ | n
  · rw [alternatingGroup.eq_bot_of_card_le_two (by simp), Subgroup.card_bot] at h
    omega
  · have : Nontrivial (Fin (2 * (n + 1))) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin] at h
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> simp_all [Nat.factorial]
    · have := Nat.factorial_le (show 8 ≤ 2 * (n + 1) by omega)
      have h8 : Nat.factorial 8 = 40320 := by decide
      omega

theorem perm_three_center (g : Equiv.Perm (Fin 3)) (hg : ∀ h, g * h = h * g) : g = 1 := by
  revert g; decide

theorem false_of_center_le_of_perm_three {Γ : Type*} [Group Γ] {Y J : Subgroup Γ}
    (hJY : J ≤ Y) (hZ : Nat.card (Subgroup.center Y) = 3)
    (hZJ : ∀ ζ ∈ Subgroup.center Y, (ζ : Γ) ∈ J)
    (ψ : J →* Equiv.Perm (Fin 3)) (hψ : Function.Surjective ψ)
    (hker : ∀ j, ψ j = 1 → ∃ k : ℕ, j ^ (2 ^ k) = 1) : False := by
  obtain ⟨ζ, hζ, hζ1, h3⟩ := exists_ne_one_of_card_center_eq_three hZ
  set j : J := ⟨ζ, hZJ ζ hζ⟩
  have hcen : ψ j = 1 := perm_three_center _ fun σ => by
    obtain ⟨k, rfl⟩ := hψ σ
    rw [← map_mul, ← map_mul]
    congr 1
    have := Subgroup.mem_center_iff.mp hζ ⟨k, hJY k.2⟩
    exact Subtype.ext (by simpa using congrArg Subtype.val this.symm)
  obtain ⟨k, hk⟩ := hker j hcen
  have hjo : orderOf j = orderOf ζ := by
    rw [← Subgroup.orderOf_coe j, ← Subgroup.orderOf_coe ζ]
  have hdvd : orderOf ζ ∣ 2 ^ k := hjo ▸ orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf ζ) (2 ^ k) :=
    Nat.Coprime.coprime_dvd_left h3 (Nat.Coprime.pow_right k (by norm_num))
  exact hζ1 (orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd))


section Core

variable {Γ : Type*} [Group Γ] [Finite Γ]


end Core

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mk_mem_barM {M X : Subgroup G} (m : M) (hm : (m : G) ∈ X) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) m ∈ barM M X :=
  ⟨m, hm, rfl⟩

theorem prop3 {p : ℕ} {P : Sylow p G} {M H R : Subgroup G} (h : D1PhaseThree p P M H R)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hZ : Nat.card (Subgroup.center ↥(barM M L)) = 3)
    (hA6 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    (hc : CenterCentralizesBlockV M (pCoreOf 2 H) L hL.le) (hns : ¬ IsShort2 L) :
    (∀ ζ ∈ Subgroup.center ↥(barM M L),
        (ζ : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ∧
      barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≠ barM M L ∧
      NineThreeTwo M (pCoreOf 2 H) L ∧
      ¬ IsSylowTwoOf (barM M (pCoreOf 2 H ⊓ L)) (barM M L) := by
  set S := pCoreOf 2 H
  have hVf := h.blockV_facts h86 hL
  have hHN : H ≤ Subgroup.normalizer (S : Set G) := localGroup_le_normalizer_pCoreOf 2 H
  have hQS : pCoreOf 2 M ≤ S := h.toD1Escape.twoCore_M_le h.twoCore_inf
  have hi : ∀ ζ ∈ Subgroup.center ↥(barM M L),
      (ζ : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L) := by
    intro ζ hζ
    obtain ⟨m, hm, hmζ⟩ := ζ.2
    have hmL : (m : G) ∈ L := hm
    have hcen : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G), hL.le hmL⟩ ∈
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_center_iff.mp hζ ⟨y, hy⟩
      have e : (⟨(m : G), hL.le hmL⟩ : M) = m := rfl
      rw [e, hmζ]
      simpa using congrArg Subtype.val this
    have hcV : (m : G) ∈ Subgroup.centralizer (blockV S L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hc (m : G) hmL hcen v hv).symm
    have hmH : (m : G) ∈ H := (hVf.2.2.2 ⟨Subgroup.mem_sup_left hmL, hcV⟩).1
    rw [← hmζ]
    exact mk_mem_barM m ⟨hHN hmH, hmL⟩
  have hJ : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≠ barM M L := by
    intro hJ
    apply hL.not_le_normalizer
    intro l hl
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hL.le hl⟩ ∈
        barM M (Subgroup.normalizer (S : Set G) ⊓ L) := hJ ▸ mk_mem_barM _ hl
    obtain ⟨m, hm, hmeq⟩ := hmem
    have hq : m⁻¹ * ⟨l, hL.le hl⟩ ∈ CFSG.pCore 2 ↥M := QuotientGroup.eq.mp hmeq
    have hqS : ((m⁻¹ * ⟨l, hL.le hl⟩ : M) : G) ∈ S := hQS ⟨_, hq, rfl⟩
    have hlm : l = (m : G) * ((m⁻¹ * ⟨l, hL.le hl⟩ : M) : G) := by simp
    rw [hlm]
    exact (Subgroup.normalizer (S : Set G)).mul_mem (Subgroup.mem_inf.mp hm).1
      (Subgroup.le_normalizer hqS)
  have h2 : NineThreeTwo M S L := by
    rcases h.nineThree h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · exact (hns h1.1).elim
    · exact h2
    · exact (hns h3.1).elim
    · exact (hns h4.1).elim
    · exact (hns h5.1).elim
    · exfalso
      obtain ⟨-, n, ⟨e1⟩, ⟨e2⟩⟩ := h6
      obtain ⟨e0⟩ := hA6
      have hcard : Nat.card (alternatingGroup (Fin (2 * n))) = 360 := by
        rw [← Nat.card_congr e1.toEquiv, Nat.card_congr e0.toEquiv]
        have : Nontrivial (Fin 6) := Fin.nontrivial_iff_two_le.mpr (by omega)
        rw [nat_card_alternatingGroup, Nat.card_fin]
        decide
      have hn := eq_three_of_card_alternatingGroup hcard
      subst hn
      set J := barM M (Subgroup.normalizer (S : Set G) ⊓ L)
      have hJL : J ≤ barM M L := Subgroup.map_mono fun x hx => (Subgroup.mem_subgroupOf.mp hx).2
      refine false_of_center_le_of_perm_three hJL hZ hi
        (e2.toMonoidHom.comp (QuotientGroup.mk' _))
        (e2.surjective.comp (QuotientGroup.mk'_surjective _)) fun j hj => ?_
      have hj1 : QuotientGroup.mk' (CFSG.pCore 2 ↥J) j = 1 := e2.map_eq_one_iff.mp hj
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hj1
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)) ⟨j, hj1⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · exfalso
      obtain ⟨-, n, ⟨e⟩, -⟩ := h7
      exact false_of_card_center_eq_three_of_alt hZ (by omega) e
    · exact (hns h8.1).elim
  exact ⟨hi, hJ, h2, (h.nineThree_not_one h85 hD2 hL).2 h2⟩


end CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6
