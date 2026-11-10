module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneDisc
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]


namespace TenElevenOneLie

theorem not_three_dvd_card_pCore_two (X : Type*) [Group X] [Finite X] :
    ¬ 3 ∣ Nat.card (CFSG.pCore 2 X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := X))
  rw [hk]
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem pRank_map_le {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (φ : X →* Y) (hker : ¬ p ∣ Nat.card φ.ker) (U : Subgroup X) :
    Open.pRank p (U.map φ) ≤ Open.pRank p U := by
  let ψ : ↥U →* ↥(U.map φ) := φ.subgroupMap U
  have hψ : Function.Surjective ψ := φ.subgroupMap_surjective U
  have hdvd : Nat.card ψ.ker ∣ Nat.card φ.ker := by
    have hle : ψ.ker.map U.subtype ≤ φ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact MonoidHom.mem_ker.mpr h
    rw [← Subgroup.card_map_of_injective U.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  have hk : p.Coprime (Nat.card ψ.ker) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hker (h.trans hdvd)
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (U.map φ),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup U,
    pRank_top_eq_of_coprime_kernel p hp ψ hψ hk]

variable {M : Subgroup G}

theorem exists_bar_of_not_centRankThreeAt (hc : ¬ CentRankThreeAt 3 M) :
    ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      Open.pRank 3 (Subgroup.centralizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ≤ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simp only [CentRankThreeAt, not_forall, not_le] at hc
  obtain ⟨E, hEM, hE, hcard, hr⟩ := hc
  have hN := not_three_dvd_card_pCore_two ↥M
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set E' : Subgroup ↥M := E.subgroupOf M
  haveI := hE.1
  have hE' : IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · change ((a : ↥M) : G) * ((b : ↥M) : G) = ((b : ↥M) : G) * ((a : ↥M) : G)
      exact congrArg Subtype.val
        (mul_comm' (⟨_, mem_subgroupOf.mp a.2⟩ : E) ⟨_, mem_subgroupOf.mp b.2⟩)
    · simpa using hE.2 _ (mem_subgroupOf.mp hx)
  have hE'p : IsPGroup 3 E' := fun x => ⟨1, Subtype.ext (by simpa using hE'.2 _ x.2)⟩
  have hinj := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype hN hE'p
  refine ⟨E'.map π, CFSG.SectionRank.isElemAbelian_map hE' π, ?_, ?_⟩
  · have hrange : E'.map π = (π.comp E'.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hEM).toEquiv, hcard]
    norm_num
  · rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hN hE'p]
    have h1 := pRank_map_le Nat.prime_three π (by rwa [QuotientGroup.ker_mk'])
      (centralizer (E' : Set ↥M))
    have h2 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) M.subtype
      M.subtype_injective (centralizer (E' : Set ↥M))
    have h3 : (centralizer (E' : Set ↥M)).map M.subtype ≤ centralizer (E : Set G) ⊓ M := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨mem_centralizer_iff.mpr fun e he => ?_, x.2⟩
      have := mem_centralizer_iff.mp hx ⟨e, hEM he⟩ (mem_subgroupOf.mpr he)
      exact congrArg Subtype.val this
    have h4 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) h3
    exact h1.trans (by omega)

theorem exists_bar_normal_index (hNI : HasNormalIndex M 3) :
    ∃ N : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), N.Normal ∧ N.index = 3 := by
  obtain ⟨N, -, hNn, hNi⟩ := hNI
  set N' : Subgroup ↥M := N.subgroupOf M
  haveI := hNn
  have hle : CFSG.pCore 2 ↥M ≤ N' := by
    intro x hx
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥M) ⟨x, hx⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf (x : ↥M ⧸ N') ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one])
    have h2 : orderOf (x : ↥M ⧸ N') ∣ 3 := hNi ▸ orderOf_dvd_natCard _
    have h3 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (by norm_num)) h1 h2
    exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)
  refine ⟨N'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)),
    hNn.map _ (QuotientGroup.mk'_surjective _), ?_⟩
  exact (Subgroup.index_map_eq N' (QuotientGroup.mk'_surjective _)
    (by rwa [QuotientGroup.ker_mk'])).trans hNi

end TenElevenOneLie


@[expose] def AGL81TenElevenOneLie (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (L W : Subgroup G) (a₀ : G),
    AGL81ElevenNineData 3 P M H Q K L W a₀ → ∀ V : Sylow 3 G, (V : Subgroup G) ≤ M →
      ¬ CentRankThreeAt 3 M → HasNormalIndex M 3 →
      (∃ e : ℕ, IsLieOver (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) (.A 2) 2 e) →
      rankThreeGamma 2 3 (V : Subgroup G) ≤ M ∨
        Nonempty ((M ⧸ primeComplementCore (G := M) 3) ≃* alternatingGroup (Fin 10)) ∨
        Nonempty ((M ⧸ primeComplementCore (G := M) 3) ≃* Equiv.Perm (Fin 10))


end CFSG.LocalAnalysis.RankThreeTheoremC
