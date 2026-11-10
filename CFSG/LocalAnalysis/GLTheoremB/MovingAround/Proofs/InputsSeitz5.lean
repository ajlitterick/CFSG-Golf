module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116c
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSmallTypes
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutElemRank

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz5

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex IsTwoPow Bal207Index IsL2EightIndex
  IsF4EightIndex IsD4FourIndex FourIndex Gen2318Index Bal209TwoIndex IsTwistedE6FourIndex Seitz2310CubeSimple)
open CFSG.AGLEmbeddingD2 (KFactSeitzRankTwo IsD2SeitzException)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple onLie ambiguousChev)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open GL83.CompFam

set_option linter.unusedSectionVars false

@[expose] def Input23_19ExcRes : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ), p.Prime → p ≠ 2 →
    GLAPPrimeCore p X = ⊥ →
    ∀ B : Subgroup X, IsElemAbelian p B → 4 ≤ CFSG.Open.pRank p B →
      CFSG.Open.pRank p B = CFSG.Open.pRank p (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) →
      p ^ (CFSG.Open.pRank p B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
        Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ExcIndex p d.1 → d.1 ≠ .tits → d.1 ≠ .suzuki 2 → ¬ IsL2EightIndex d.1 →
        (IsSixIndex d.1 → ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        (Subgroup.center ↥K ≠ ⊥ ∨ B ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∨
          IsD2SeitzException p d.1) →
        K ≤ GLBCore p 2 B

@[expose] def Rank3CuResExcRes : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139b p M D → ∀ {U : Subgroup G}, IsU1312 p B M D L0 d U →
      ∀ u ∈ U, u ≠ 1 →
        CFSG.Open.pRank 3 B < CFSG.Open.pRank 3 (⊤ : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) →
        ∀ Kc : Subgroup G, GLAPComponent 3 (Cg u) Kc → Prop1310a5b.Good2319 (barOf 3 Kc) →
          B ≤ Subgroup.normalizer (Kc : Set G) →
          CFSG.Open.pRank 3 B < 2 + CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 Kc))) →
          CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
            Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
              Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1 →
          ¬ IsPiGroup 3 (barOf 3 Kc) →
          IsStronglyLocallyOneBalanced 3 B u Kc →
          ((∃ n : ℕ, 9 ≤ n ∧ n % 3 ≠ 2 ∧ IsAltType n (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc))) ∨
            ∃ i : TauCeti.ValidLieTypeIndex,
              Nonempty (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group) ∧
              i.1.characteristic ≠ 3 ∧
              ExcIndex 3 i.1 ∧ i.1 ≠ .tits ∧ ¬ IsL2EightIndex i.1 ∧
              (IsSixIndex i.1 → ¬ InputsSeitz3.autIm (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≤
                (MulAut.conj : ↥(barX 3 (Cg u) Kc) →* MulAut ↥(barX 3 (Cg u) Kc)).range) ∧
              (Subgroup.center (barOf 3 Kc) ≠ ⊥ ∨
                barX 3 (Cg u) B ⊓
                  Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
                    Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) = ⊥ ∨
                IsD2SeitzException 3 i.1)) →
          Kc ≤ M

theorem characteristic_eq_two_of_excIndex {p : ℕ} {d : TauCeti.LieTypeIndex} (h : ExcIndex p d) :
    d.characteristic = 2 := by
  by_contra hc
  cases d <;> simp_all [ExcIndex, Bal207Index, IsL2EightIndex, Gen2318Index, Bal209TwoIndex,
    IsTwistedE6FourIndex, IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex, IsTwoPow]

theorem eq_three_or_five_of_excIndex_tits {p : ℕ} (h : ExcIndex p .tits) : p = 3 ∨ p = 5 := by
  rcases h with h | ⟨h, -⟩
  · exact h
  · exact Or.inl h

theorem eq_five_of_excIndex_suzuki {p m : ℕ} (h : ExcIndex p (.suzuki m)) : p = 5 := by
  rcases h with h | ⟨-, h⟩
  · simp only [Bal207Index] at h
    exact h.1
  · simp [IsL2EightIndex, Gen2318Index, Bal209TwoIndex, IsTwistedE6FourIndex, IsSixIndex, IsF4EightIndex,
      IsD4FourIndex, FourIndex] at h

theorem eq_three_of_excIndex_A {p r : ℕ} {q : TauCeti.PrimePower} (h : ExcIndex p (.A r q)) : p = 3 := by
  rcases h with h | ⟨h, -⟩
  · simp [Bal207Index] at h
  · exact h

theorem autIm_mono {Y : Type} [Group Y] {E B : Subgroup Y} (h : E ≤ B) (K : Subgroup Y) :
    InputsSeitz3.autIm E K ≤ InputsSeitz3.autIm B K := by
  rintro _ ⟨n, hn, rfl⟩
  exact ⟨n, Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hn)), rfl⟩

theorem pRank_mulAut_le_quot {p : ℕ} (hp : p.Prime) {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (K ⧸ Subgroup.center K))) :=
  CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (quotientCenterAut' K)
    (quotientCenterAut'_injective hperf)

section Dispatch


theorem pRank_three_mulAut_le_two_of_tits
    {S : Type} [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .tits)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut S)) ≤ 2 := by
  obtain ⟨d0, hv⟩ := d
  simp only at hd
  subst hd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := GL83.CompFam.exists_card_eq_pow hE
  have hk3 : 3 ≤ k := by
    by_contra h
    push Not at h
    have h1 : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hk] at hlt
    exact absurd hlt (not_lt.2 h1)
  obtain ⟨D, hD⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (show 3 ^ 3 ∣ Nat.card E by rw [hk]; exact pow_dvd_pow 3 hk3)
  set φ : MulAut S →* MulAut (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := (MulAut.congr e).toMonoidHom
  have hφ : Function.Injective φ := (MulAut.congr e).injective
  have hDel : IsElemAbelian 3 ((D.map E.subtype).map φ) :=
    CFSG.SectionRank.isElemAbelian_map (elem_mono hE (Subgroup.map_subtype_le D)) φ
  refine CFSG.HardMathSupport.Timmesfeld.CrossChar.titsNoElemAbelian27 hv _ hDel ?_
  rw [Subgroup.card_map_of_injective hφ, Subgroup.card_map_of_injective E.subtype_injective, hD]
  norm_num

theorem pRank_five_mulAut_le_two_of_suzuki
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .suzuki 2) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut S)) ≤ 2 := by
  obtain ⟨d0, hv⟩ := d
  simp only at hd
  subst hd
  have hX : CFSG.Blueprint.LieModel S .twistedB2 0 2 (2 * 2 + 1) :=
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
        (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_lie (t := .twistedB2) (p := 2)
          (f := 2 * 2 + 1) ⟨Nat.prime_two, by omega, rfl, rfl, ⟨2, rfl⟩, by omega⟩ ⟨.suzuki 2, hv⟩
          ⟨rfl, rfl⟩))
  have hS : CFSG.Blueprint.SuzukiModel S 2 (2 * 2 + 1) := (CFSG.Blueprint.LieModel.suzukiModel hX).2
  have hZ : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple hs hnab
  refine (CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_add_pRank_outer Nat.prime_five hZ).trans ?_
  have h1 : CFSG.Open.pRank 5 (⊤ : Subgroup S) ≤ 1 :=
    CFSG.QuasithinUnique.Id2519.pRank_le_one_suzuki hS Nat.prime_five (by norm_num)
  haveI hcyc : IsCyclic (Outer S) :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} S 2 _ hS).1.1
  have h2 : CFSG.Open.pRank 5 (⊤ : Subgroup (Outer S)) ≤ 1 :=
    CFSG.LocalAnalysis.RankFourTheoremC.pRank_le_one_of_isCyclic Nat.prime_five inferInstance
  omega

theorem pRank_mulAut_le_two_of_small {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    {p : ℕ} (d : TauCeti.ValidLieTypeIndex) (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hexc : ExcIndex p d.1) (hd : d.1 = .tits ∨ d.1 = .suzuki 2 ∨ IsL2EightIndex d.1) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  have hs : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.exists_noncomm_quot hq
  rcases hd with hd | hd | hd
  · rw [hd] at hexc
    rcases eq_three_or_five_of_excIndex_tits hexc with rfl | rfl
    · exact (pRank_mulAut_le_quot Nat.prime_three hq.1).trans (pRank_three_mulAut_le_two_of_tits d hd e)
    · exact InputsSeitz3.pRank_five_mulAut_le_two_of_tits hq.1 d hd e
  · rw [hd] at hexc
    obtain rfl := eq_five_of_excIndex_suzuki hexc
    exact (pRank_mulAut_le_quot Nat.prime_five hq.1).trans
      (pRank_five_mulAut_le_two_of_suzuki hs hnab d hd e)
  · obtain ⟨q, hdq, hq3⟩ := hd.exists
    rw [hdq] at hexc
    obtain rfl := eq_three_of_excIndex_A hexc
    exact (pRank_mulAut_le_quot Nat.prime_three hq.1).trans
      (CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_two_of_l28
        (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple hs hnab)
        ⟨q, hdq, hq3.1, hq3.2⟩ e)


end Dispatch


section Rank3


end Rank3

section Holds


end Holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz5

end
