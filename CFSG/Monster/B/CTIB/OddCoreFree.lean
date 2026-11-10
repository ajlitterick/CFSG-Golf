module

public import CFSG.Monster.B.CTIB.Rank2168Final
public import CFSG.Monster.B.CTIB.DistThreeProductFinal
public import CFSG.RankThree.OddKernel.OddLift

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.LieType.Chevalley.C2E6Std
open CFSG.Sporadic.Co2Inv (co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

section Generic

variable {G : Type*} [Group G]

theorem oddCore_eq_bot_iff :
    CFSG.oddCore G = ⊥ ↔ ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥ := by
  rw [CFSG.oddCore, sSup_eq_bot]
  exact ⟨fun h N hN hodd => h N ⟨hN, hodd⟩, fun h N hN => h N hN.1 hN.2⟩

theorem oddCore_eq_bot_of_equiv {H : Type*} [Group H] (e : G ≃* H) (h : CFSG.oddCore G = ⊥) :
    CFSG.oddCore H = ⊥ := by
  refine oddCore_eq_bot_iff.2 fun N hNn hN => ?_
  have h1 := oddCore_eq_bot_iff.1 h (N.map e.symm.toMonoidHom) (hNn.map _ e.symm.surjective)
    ((Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective).symm ▸ hN)
  exact (Subgroup.map_eq_bot_iff_of_injective (f := e.symm.toMonoidHom) _ e.symm.injective).1 h1

theorem eq_bot_of_selfCent [Finite G] {R N : Subgroup G} (hRn : R.Normal) (hR2 : IsPGroup 2 R)
    (hRc : Subgroup.centralizer (R : Set G) ≤ R) (hNn : N.Normal) (hN : Odd (Nat.card N)) :
    N = ⊥ := by
  have hinf : N ⊓ R = ⊥ :=
    (inf_comm N R).trans (CFSG.RankThree.OddKernel.inf_eq_bot_of_odd hR2 hN)
  have hc : ⁅N, R⁆ = ⊥ := le_bot_iff.1 ((Subgroup.commutator_le_inf N R).trans hinf.le)
  have hNR : N ≤ R := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc).trans hRc
  exact le_bot_iff.1 ((le_inf le_rfl hNR).trans hinf.le)

theorem oddCore_eq_bot_of_selfCent [Finite G]
    (h : ∃ R : Subgroup G, R.Normal ∧ IsPGroup 2 R ∧ Subgroup.centralizer (R : Set G) ≤ R) :
    CFSG.oddCore G = ⊥ := by
  obtain ⟨R, hRn, hR2, hRc⟩ := h
  exact oddCore_eq_bot_iff.2 fun N hNn hN => eq_bot_of_selfCent hRn hR2 hRc hNn hN

theorem le_of_odd_of_card_quotient [Finite G] {M N : Subgroup G} [M.Normal] {k : ℕ}
    (hM : Nat.card (G ⧸ M) = 2 ^ k) (hN : Odd (Nat.card N)) : N ≤ M := by
  have h1 := Subgroup.card_map_dvd N (QuotientGroup.mk' M)
  have h2 : Nat.card (N.map (QuotientGroup.mk' M)) ∣ 2 ^ k :=
    hM ▸ Subgroup.card_subgroup_dvd_card _
  have hj := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  obtain ⟨j, -, hj⟩ := hj
  have hodd := hN.of_dvd_nat h1
  rw [hj] at hodd
  have hj0 : j = 0 := by
    by_contra h
    exact Nat.not_even_iff_odd.2 hodd ((Nat.even_pow' h).2 even_two)
  have hbot := Subgroup.eq_bot_of_card_eq _ (hj.trans (by rw [hj0, pow_zero]))
  exact (QuotientGroup.ker_mk' M) ▸ (Subgroup.map_eq_bot_iff N).1 hbot

theorem oddCore_eq_bot_of_quotient [Finite G] {M : Subgroup G} [M.Normal] {k : ℕ}
    (hM : Nat.card (G ⧸ M) = 2 ^ k) (hMo : CFSG.oddCore M = ⊥) : CFSG.oddCore G = ⊥ := by
  refine oddCore_eq_bot_iff.2 fun N hNn hN => ?_
  have hNM := le_of_odd_of_card_quotient hM hN
  have : N.Normal := hNn
  have hcard : Nat.card (N.subgroupOf M) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have h1 := oddCore_eq_bot_iff.1 hMo (N.subgroupOf M) inferInstance (hcard ▸ hN)
  have h2 := Subgroup.subgroupOf_map_subtype N M
  rw [h1, Subgroup.map_bot, inf_eq_left.2 hNM] at h2
  exact h2.symm

theorem oddCore_eq_bot_of_isSimpleGroup (hs : IsSimpleGroup G) (he : Even (Nat.card G)) :
    CFSG.oddCore G = ⊥ := by
  refine oddCore_eq_bot_iff.2 fun N hNn hN => ?_
  have : N.Normal := hNn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · rw [h, Subgroup.card_top] at hN
    exact absurd he (Nat.not_even_iff_odd.2 hN)

theorem oddCore_eq_bot_of_quotient_simple [Finite G] {Z : Subgroup G} [Z.Normal]
    (hZ : Nat.card Z = 2) (hs : IsSimpleGroup (G ⧸ Z)) (he : Even (Nat.card (G ⧸ Z))) :
    CFSG.oddCore G = ⊥ := by
  refine oddCore_eq_bot_iff.2 fun N hNn hN => ?_
  have : (N.map (QuotientGroup.mk' Z)).Normal := hNn.map _ (QuotientGroup.mk'_surjective Z)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Z)) with h | h
  · have hNZ : N ≤ Z := (QuotientGroup.ker_mk' Z) ▸ (Subgroup.map_eq_bot_iff N).1 h
    have hdvd : Nat.card N ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le hNZ
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · rw [h2] at hN
      exact absurd hN (by decide)
  · have hdvd := Subgroup.card_map_dvd N (QuotientGroup.mk' Z)
    rw [h, Subgroup.card_top] at hdvd
    exact absurd he (Nat.not_even_iff_odd.2 (hN.of_dvd_nat hdvd))

end Generic

theorem oddCore_Eam :
    CFSG.oddCore Eam = ⊥ := by
  have hD := derivedCoverInput_holds
  obtain ⟨hidx, -, -, hcen, hc2, hθ, -, hcard⟩ := hD
  obtain ⟨θ⟩ := hθ
  have hq : Nat.card (Eam ⧸ commutator Eam) = 2 ^ 1 :=
    (Subgroup.index_eq_card _).symm.trans (hidx.trans (pow_one 2).symm)
  refine oddCore_eq_bot_of_quotient hq ?_
  have hle : Subgroup.zpowers cE' ≤ commutator Eam :=
    hcen ▸ Subgroup.map_subtype_le _
  have hZ : Nat.card ((Subgroup.zpowers cE').subgroupOf (commutator Eam)) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans hc2
  have hs : IsSimpleGroup
      (commutator Eam ⧸ (Subgroup.zpowers cE').subgroupOf (commutator Eam)) :=
    @MulEquiv.isSimpleGroup _ _ _ _ stdGroup_simple θ
  have hcq := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Subgroup.zpowers cE').subgroupOf (commutator Eam))
  rw [hZ, hcard] at hcq
  have he : Nat.card (commutator Eam ⧸ (Subgroup.zpowers cE').subgroupOf (commutator Eam)) =
      76532479683774853939200 := by omega
  exact oddCore_eq_bot_of_quotient_simple hZ hs (he ▸ (by decide))

theorem oddCore_rank1860
    {t : Sbp} (ht : orderOf t = 2) (hr : ((βr t) - 1).rank = 1860) :
    CFSG.oddCore (Subgroup.centralizer {t}) = ⊥ := by
  have hE := centralizer_equiv_Eam (centralizerInput_of_ambient ambientRootOrbitsHyp)
    (isConj_labelS_of_rank ht hr)
  obtain ⟨Ψ⟩ := hE
  exact oddCore_eq_bot_of_equiv Ψ.symm oddCore_Eam

theorem oddCore_rank2048
    {t : Sbp} (ht : orderOf t = 2) (hr : ((βr t) - 1).rank = 2048) :
    CFSG.oddCore (Subgroup.centralizer {t}) = ⊥ := by
  have h := native_rank_2048_centralizer_has_no_components t ht hr
  obtain ⟨-, -, -, -, Q, -, hQn, hQ, -, hcen, -⟩ := h
  exact oddCore_eq_bot_of_selfCent ⟨Q, hQn, hQ.1, hcen ▸ Subgroup.map_subtype_le _⟩

theorem oddCore_rank2168
    {t : Sbp} (ht : orderOf t = 2) (hr : ((βr t) - 1).rank = 2168) :
    CFSG.oddCore (Subgroup.centralizer {t}) = ⊥ :=
  oddCore_eq_bot_of_selfCent (native_rank_2168_centralizer_has_no_components t ht hr).1

theorem oddCore_distThree
    {v w : CVert} (hvw : cgraph.dist v w = 3) :
    CFSG.oddCore (Subgroup.centralizer {clabelS v * clabelS w} : Subgroup Shat) = ⊥ := by
  have h := distance_three_product_full_centralizer_final hvw rfl rfl rfl
  obtain ⟨-, -, hRC, -, hFn, -, -, hq8, hFc, -, -, -, hFs, -⟩ := h
  have : ((⁅Subgroup.centralizer {clabelS v, clabelS w},
      Subgroup.centralizer {clabelS v, clabelS w}⁆ : Subgroup Shat).subgroupOf
        (Subgroup.centralizer {clabelS v * clabelS w})).Normal := hFn
  refine oddCore_eq_bot_of_quotient (k := 3) (hq8.trans (by norm_num)) ?_
  have hFC := (commutator_self_le (Subgroup.centralizer ({clabelS v, clabelS w} : Set Shat))).trans
    hRC
  exact oddCore_eq_bot_of_equiv (Subgroup.subgroupOfEquivOfLe hFC).symm
    (oddCore_eq_bot_of_isSimpleGroup hFs (hFc ▸ (by decide)))

theorem oddCore_rank2158
    {t : Sbp} (ht : orderOf t = 2) (hr : ((βr t) - 1).rank = 2158) :
    CFSG.oddCore (Subgroup.centralizer {t}) = ⊥ := by
  have hw := exists_witness_pair ambientRootOrbitsHyp
  obtain ⟨v, u, hvu, hd⟩ := hw
  have hΨ := centralizer_equiv_of_isConj
    ((isConj_rs5_of_rank ht hr).trans isConj_rs6_mul_e2158.symm)
  obtain ⟨Ψ₁⟩ := hΨ
  have Ψ₂ : Subgroup.centralizer {rs 6 * e2158} ≃*
      Subgroup.centralizer {clabelS v * clabelS u} :=
    (centralizerEquiv sEquiv (rs 6 * e2158)).trans (MulEquiv.subgroupCongr
      (congrArg (fun y : Shat => Subgroup.centralizer {y}) hd.symm))
  exact oddCore_eq_bot_of_equiv (Ψ₁.trans Ψ₂).symm (oddCore_distThree hvu)

theorem native_B_all_involution_centralizers_odd_core_free :
    (∀ t : Sbp, orderOf t = 2 → CFSG.oddCore (Subgroup.centralizer {t}) = ⊥) ∧
    (∀ t : Cbar, orderOf t = 2 → CFSG.oddCore (Subgroup.centralizer {t}) = ⊥) ∧
    (∀ t : Shat, orderOf t = 2 → CFSG.oddCore (Subgroup.centralizer {t}) = ⊥) := by
  have hS : ∀ t : Sbp, orderOf t = 2 → CFSG.oddCore (Subgroup.centralizer {t}) = ⊥ := by
    intro t ht
    obtain ⟨i, ⟨hi, hc⟩, -⟩ := four_classes co2_involution_input ht
    have e := rank_beta_conj hc
    obtain ⟨h1, h0, h5, h3⟩ := rank_four
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact oddCore_rank1860 ht (e.trans h1)
    · exact oddCore_rank2048 ht (e.trans h0)
    · exact oddCore_rank2158 ht (e.trans h5)
    · exact oddCore_rank2168 ht (e.trans h3)
  refine ⟨hS, fun t ht => ?_, fun t ht => ?_⟩
  · have h := hS (MulEquiv.inv' Cbar t) ((MulEquiv.orderOf_eq _ t).trans ht)
    exact oddCore_eq_bot_of_equiv (centralizerEquiv (MulEquiv.inv' Cbar) t).symm h
  · have h := hS (sEquiv.symm t) ((MulEquiv.orderOf_eq _ t).trans ht)
    exact oddCore_eq_bot_of_equiv (centralizerEquiv sEquiv.symm t).symm h

end CFSG.Monster.B.CTIB
