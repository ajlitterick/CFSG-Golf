module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenExtremal
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111PsiLevel
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111KappaMoves
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAZNAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3
public import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms
open Hyp111 CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G] {p : ℕ}


theorem false_of_layer_eq_bot_of_surjective [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    {T : Sylow p X} {X₀ : Subgroup X} (h : ReducedNongeneration p X T X₀)
    (hlayer : CFSG.layer X = ⊥) {J : Subgroup X} {S : Type*} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) (φ : J →* S)
    (hφ : Function.Surjective φ) (hS2 : p ^ 2 ∣ Nat.card S) : False := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, hET, -, hEc⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp h.three_le_pRank
  haveI : Nontrivial (T : Subgroup X) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have h1 : Nat.card E ≤ Nat.card (T : Subgroup X) := Subgroup.card_le_of_le hET
    have h2 : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  haveI := IsPGroup.center_nontrivial T.isPGroup'
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (T.isPGroup'.to_subgroup (Subgroup.center T))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hk
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (by rw [hk]; exact dvd_pow_self p hk0)
  have hzc : ((z : T) : X) ∈ Subgroup.centralizer ((T : Subgroup X) : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun r hr =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨r, hr⟩)
  have hzo : orderOf ((z : T) : X) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hz
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrel, -, -⟩ :=
    h.structure_of_layer_eq_bot3 hlayer hzc hzo
  set Q := CFSG.pCore p X
  have hQn : Q.Normal := CFSG.pCore_normal
  have hQp : IsPGroup p Q := CFSG.pCore_isPGroup
  have hQT : Q ≤ (T : Subgroup X) := hQp.le_sylow_of_normal T
  set D := Q.subgroupOf J
  have hDker : D ≤ φ.ker := by
    have hDn : (D.map φ).Normal := (Subgroup.normal_subgroupOf).map φ hφ
    haveI := hS
    haveI := hDn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.map φ) with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).mp hb
    · exfalso
      have hSp : IsPGroup p S := by
        have hDp : IsPGroup p D := hQp.comap_subtype
        have := hDp.map φ
        rw [ht] at this
        exact this.of_equiv Subgroup.topEquiv
      haveI : Nontrivial S := inferInstance
      have hc := IsPGroup.center_nontrivial hSp
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hb | ht
      · exact (Subgroup.nontrivial_iff_ne_bot _).mp hc hb
      · obtain ⟨a, b, hab⟩ := hSnab
        exact hab (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top b) a)
  have hJ1 : Nat.card S * Nat.card φ.ker = Nat.card J := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker).symm
  have hDdvd : Nat.card D ∣ Nat.card φ.ker := Subgroup.card_dvd_of_le hDker
  have hidx := Subgroup.index_mul_card D
  have hpos : 0 < Nat.card D := Nat.card_pos
  have h2 : p ^ 2 ∣ Q.relIndex J := by
    obtain ⟨c, hc⟩ := hDdvd
    have : Nat.card S * c = D.index := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [hidx, ← hJ1, hc]; ring
    exact (hS2.trans (Dvd.intro c this))
  rw [← Subgroup.relIndex_sup_right J Q] at h2
  have e1 := Subgroup.relIndex_mul_card (H := Q) (K := J ⊔ Q)
  rw [inf_of_le_left le_sup_right] at e1
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
  have h3 : p ^ (2 + n) ∣ Nat.card X := by
    rw [pow_add, ← hn]
    exact (Nat.mul_dvd_mul_right h2 _).trans (e1 ▸ Subgroup.card_subgroup_dvd_card _)
  have h4 := T.pow_dvd_card_of_pow_dvd_card h3
  have e2 := Subgroup.relIndex_mul_card (H := Q) (K := (T : Subgroup X))
  rw [inf_of_le_left hQT, hrel, hn, ← pow_succ'] at e2
  rw [← e2] at h4
  have := Nat.pow_dvd_pow_iff_le_right hp.one_lt |>.mp h4
  omega


theorem exists_surjective_cover [Fact p.Prime] {H N : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKs : IsSimpleGroup K)
    (hKp : ∃ x : K, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1) (hcov : AGLCovers p H N K) :
    ∃ (J : Subgroup (N ⧸ primeComplementCore (G := N) p)) (φ : J →* K), Function.Surjective φ := by
  set πH := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set πN := QuotientGroup.mk' (primeComplementCore (G := N) p)
  set W₀ : Subgroup G := (H ⊓ N) ⊓ (K.comap πH).map H.subtype with hW₀def
  have hW₀H : W₀ ≤ H := inf_le_left.trans inf_le_left
  have hW₀N : W₀ ≤ N := inf_le_left.trans inf_le_right
  have hW₀K : ∀ {g : G} (hg : g ∈ W₀), πH ⟨g, hW₀H hg⟩ ∈ K := by
    rintro g ⟨-, h, hh, hhg⟩
    have : h = ⟨g, hW₀H ⟨‹_›, h, hh, hhg⟩⟩ := Subtype.ext hhg
    exact this ▸ hh
  have hψ₀ : ∀ w : W₀, πH (Subgroup.inclusion hW₀H w) ∈ K := fun w => hW₀K w.2
  set ψ : W₀ →* K := (πH.comp (Subgroup.inclusion hW₀H)).codRestrict K hψ₀
  have hψs : Function.Surjective ψ := by
    rintro ⟨k, hk⟩
    obtain ⟨h, hh, rfl⟩ := hcov hk
    have hhN : (h : G) ∈ H ⊓ N := Subgroup.mem_subgroupOf.mp hh
    exact ⟨⟨h, hhN, h, hk, rfl⟩, rfl⟩
  set ρ : W₀ →* N ⧸ primeComplementCore (G := N) p := πN.comp (Subgroup.inclusion hW₀N)
  obtain ⟨x, hx1, kx, hxk⟩ := hKp
  haveI := hKs
  have hker : ρ.rangeRestrict.ker ≤ ψ.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact le_ker_of_isSimpleGroup ψ hψs ρ.ker
      (fun n hn => coprime_of_mk_inclusion_eq_one3 hW₀N n hn) hx1 hxk
  obtain ⟨φ₀, -, hφ₀s, -⟩ := exists_surjective_comp_eq ρ.rangeRestrict
    ρ.rangeRestrict_surjective ψ hψs hker
  exact ⟨ρ.range, φ₀, hφ₀s⟩


end CFSG.LocalAnalysis.RankThreeTheoremC
