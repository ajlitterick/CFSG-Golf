module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnMain
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf)
open CFSG.ClassicalInvolution.Balance.Theorem5
  (MemberClass conjMembers commuteAdj FuzzyEdgeInFrame FuzzyLinkConn FuzzyFrameBalance
    fuzzyFrames fuzzyVertices conjInvariant_conjMembers fuzzyAxisExact_conjMembers
    fuzzyMemberConn_conjMembers fuzzyVertexConn_of_adj)

section Residual

theorem perfectResidual_eq_of_sup_solvable {H : Type*} [Group H] [Finite H] {P N : Subgroup H}
    (hP : Group.IsPerfect P) (hPn : P.Normal) (hN : N.Normal) (hNsol : Group.IsSolvable N)
    (hPN : P ⊔ N = ⊤) : CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual H = P := by
  apply le_antisymm
  · have hsurj : Function.Surjective ((QuotientGroup.mk' P).comp N.subtype) := by
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective P y
      have hh : h ∈ N ⊔ P := by
        rw [sup_comm, hPN]
        exact Subgroup.mem_top h
      obtain ⟨n, hn, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hh
      refine ⟨⟨n, hn⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff q).mpr hq,
        mul_one]
    have hsol : Group.IsSolvable (H ⧸ P) := Group.isSolvable_of_surjective hsurj
    exact ((CFSG.perfect_residual_characterization (G := H)).2.2.2.2.1 P).mp hsol
  · exact (CFSG.perfect_residual_transport (MonoidHom.id H)).2.2 P hP

end Residual

section Canon

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem canonMember_eq_of_isClassicalMember {J : Subgroup G} {z : G}
    (hJ : IsClassicalMember p f J z) : canonMember J z = J := by
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hN : involutionOddCore z = oddCoreIn C := involutionOddCore_eq_oddCoreIn z
  set N : Subgroup G := involutionOddCore z with hNdef
  have hNtq : N ≤ trivialOnQuot J := by
    rw [hN]
    exact oddCoreIn_le_trivialOnQuot hJ.subnormal hJ.perfect
  set Z : Subgroup G := J ⊔ N with hZ
  have hJZ : J ≤ Z := le_sup_left
  have hNZ : N ≤ Z := le_sup_right
  have hZnorm : Z ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer fun n hn => (hNtq hn).1
  have hJn : (J.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJZ).mpr hZnorm
  have hJC : J ≤ C := isSubnormal_le hJ.subnormal
  have hNC : N ≤ C := by
    rw [hN]
    exact oddCoreIn_le C
  have hZC : Z ≤ C := sup_le hJC hNC
  have hNn : (N.subgroupOf Z).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNZ]
    refine hZC.trans ?_
    rw [hN]
    exact normalizer_oddCoreIn C
  have hNodd : Odd (Nat.card ↥(N.subgroupOf Z)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNZ).toEquiv, hN]
    exact odd_card_oddCoreIn C
  have hNsol : Group.IsSolvable ↥(N.subgroupOf Z) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  have := hJ.perfect
  have hperf : Group.IsPerfect ↥(J.subgroupOf Z) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJZ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJZ).symm.surjective
  have hsup : J.subgroupOf Z ⊔ N.subgroupOf Z = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hJZ hNZ, ← hZ]
    exact Subgroup.subgroupOf_self Z
  have h := perfectResidual_eq_of_sup_solvable hperf hJn hNn
    hNsol hsup
  show perfectResidualOf Z = J
  unfold perfectResidualOf
  rw [h, Subgroup.map_subgroupOf_eq_of_le hJZ]

theorem isCanonical_of_isClassicalMember {J : Subgroup G} {z : G}
    (hJ : IsClassicalMember p f J z) : IsCanonical J z :=
  canonMember_eq_of_isClassicalMember hJ

theorem canonClass_eq_conjClass {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z) :
    canonClass p f K = CoreAssembly.conjClass K := by
  ext J
  constructor
  · rintro ⟨M, hM, w, hw, rfl⟩
    rwa [canonMember_eq_of_isClassicalMember hw]
  · rintro hJ
    obtain ⟨g, rfl⟩ := hJ
    exact ⟨conjSub g K, ⟨g, rfl⟩, g * z * g⁻¹, hz.conj g,
      (canonMember_eq_of_isClassicalMember (hz.conj g)).symm⟩

end Canon

section Conj


end Conj

end CFSG.ClassicalInvolution.Balance.Bootstrap
