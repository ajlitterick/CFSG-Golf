module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderSuzukiInner
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

@[expose] def NativeBenderType (Q : Type) [Group Q] : Prop :=
  (∃ m : ℕ, 3 ≤ m ∧ Nonempty (Q ≃* PSL(2, GaloisField 2 m))) ∨
    (∃ m : ℕ, 2 ≤ m ∧ Nonempty (Q ≃* PSU3 2 m)) ∨
    ∃ a : ℕ, 1 ≤ a ∧ Nonempty (Q ≃* Sz a)

section Models

variable {Q : Type} [Group Q]

theorem nonempty_mulEquiv_psl2_of_stated {m : ℕ} (h : StatedClassicalModel Q .PSL 2 2 m) :
    Nonempty (Q ≃* PSL(2, GaloisField 2 m)) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 m hadm.2.1 hK)⟩

theorem stated_psl2_of_mulEquiv {m : ℕ} (hm : 3 ≤ m) (e : Q ≃* PSL(2, GaloisField 2 m)) :
    StatedClassicalModel Q .PSL 2 2 m := by
  have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact statedClassicalModel_psl_two_of_mulEquiv Q 2 m (by omega) e

theorem nonempty_mulEquiv_psu3_of_stated {m : ℕ} (hm : 2 ≤ m)
    (h : StatedClassicalModel Q .PSU 3 2 m) : Nonempty (Q ≃* PSU3 2 m) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hcard : Nat.card K = 2 ^ (2 * m) := by rw [hK, ← pow_mul, mul_comm]
  let e' : Q ≃* GLAProj (GLASUGroup (Fin 3) K (2 ^ m)) := e
  exact ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative m hm hcard)⟩

theorem stated_psu3_of_mulEquiv {m : ℕ} (hm : 2 ≤ m) (e : Q ≃* PSU3 2 m) :
    StatedClassicalModel Q .PSU 3 2 m := by
  have hcard : Nat.card (GaloisField 2 (2 * m)) = 2 ^ (2 * m) := GaloisField.card 2 _ (by omega)
  have hc : Nat.card (GaloisField 2 (2 * m)) = (2 ^ m) ^ 2 := by
    rw [hcard, ← pow_mul, mul_comm]
  let e' : Q ≃* StatedProj (StatedSU 3 (2 ^ m) (GaloisField 2 (2 * m))) :=
    e.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative m hm hcard).symm
  exact ⟨CFSG.ShultStronglyClosedTI.unitaryCover_psu_admissible m hm, GaloisField 2 (2 * m),
    inferInstance, inferInstance, hc, ⟨e'⟩⟩

theorem exists_mulEquiv_sz_of_suzukiModel {f : ℕ} (h : CFSG.Blueprint.SuzukiModel Q 2 f) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ Nonempty (Q ≃* Sz a) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  exact ⟨a, ha, rfl, ⟨e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))⟩⟩

theorem suzukiModel_of_mulEquiv {a : ℕ} (ha : 1 ≤ a) (e : Q ≃* Sz a) :
    CFSG.Blueprint.SuzukiModel Q 2 (2 * a + 1) := by
  have hcard : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  refine ⟨rfl, a, ha, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl, hcard, ⟨?_⟩⟩
  exact (e.trans (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard).symm).trans
    (MulEquiv.subgroupCongr
      (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a (GaloisField 2 (2 * a + 1))).symm)

theorem rankTwoBenderType_iff : RankTwoBenderType Q ↔ NativeBenderType Q := by
  constructor
  · rintro (⟨m, hm, h⟩ | ⟨m, hm, h⟩ | ⟨m, hm, h⟩)
    · exact Or.inl ⟨m, hm, nonempty_mulEquiv_psl2_of_stated h⟩
    · exact Or.inr (Or.inl ⟨m, hm, nonempty_mulEquiv_psu3_of_stated hm h⟩)
    · obtain ⟨a, ha, -, he⟩ := exists_mulEquiv_sz_of_suzukiModel h
      exact Or.inr (Or.inr ⟨a, ha, he⟩)
  · rintro (⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩)
    · exact Or.inl ⟨m, hm, stated_psl2_of_mulEquiv hm e⟩
    · exact Or.inr (Or.inl ⟨m, hm, stated_psu3_of_mulEquiv hm e⟩)
    · exact Or.inr (Or.inr ⟨a, ha, suzukiModel_of_mulEquiv ha e⟩)

theorem NativeBenderType.of_mulEquiv {Q' : Type} [Group Q'] (e : Q ≃* Q')
    (h : NativeBenderType Q') : NativeBenderType Q := by
  rcases h with ⟨m, hm, ⟨e'⟩⟩ | ⟨m, hm, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨m, hm, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨m, hm, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.trans e'⟩⟩)

theorem RankTwoBenderType.of_mulEquiv {Q' : Type} [Group Q'] (e : Q ≃* Q')
    (h : RankTwoBenderType Q') : RankTwoBenderType Q :=
  rankTwoBenderType_iff.mpr ((rankTwoBenderType_iff.mp h).of_mulEquiv e)

theorem NativeBenderType.fusionIsBenderGroup (h : NativeBenderType Q) : fusionIsBenderGroup Q := by
  rcases h with ⟨m, hm, he⟩ | ⟨m, hm, he⟩ | ⟨a, ha, he⟩
  · exact Or.inl ⟨m, by omega, he⟩
  · exact Or.inr (Or.inl ⟨m, hm, he⟩)
  · exact Or.inr (Or.inr ⟨a, ha, he⟩)

theorem NativeBenderType.finite (h : NativeBenderType Q) : Finite Q := by
  rcases h with ⟨m, -, ⟨e⟩⟩ | ⟨m, -, ⟨e⟩⟩ | ⟨a, -, ⟨e⟩⟩
  · exact Finite.of_equiv _ e.symm.toEquiv
  · have : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * m))) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    have : Finite (PSU3 2 m) := Finite.of_injective Subtype.val Subtype.coe_injective
    exact Finite.of_equiv _ e.symm.toEquiv
  · exact Finite.of_equiv _ e.symm.toEquiv

theorem NativeBenderType.isSimpleGroup (h : NativeBenderType Q) :
    IsSimpleGroup Q := by
  have := h.finite
  exact RankTwoBender.isSimpleGroup_of_bender h.fusionIsBenderGroup


end Models

section Center

theorem commutator_eq_top_of_surjective {X Y : Type*} [Group X] [Group Y] {f : X →* Y}
    (hf : Function.Surjective f) (hX : commutator X = ⊤) : commutator Y = ⊤ := by
  have h : (commutator X).map f = commutator Y := by
    rw [commutator_def, commutator_def, map_commutator, map_top_of_surjective f hf]
  rw [← h, hX, map_top_of_surjective f hf]

variable {A : Type} [Group A] [Finite A]

theorem exists_two_cover (hA : commutator A = ⊤) :
    ∃ (E : Type) (_ : Group E) (_ : Finite E) (_ : Group.IsPerfect E) (η : E →* A ⧸ center A),
      Function.Surjective η ∧ η.ker ≤ center E ∧ IsPGroup 2 η.ker ∧
        (η.ker = ⊥ → Odd (Nat.card (center A))) := by
  classical
  set N := CFSG.LieType.Steinberg.oddPart (center A) le_rfl with hNdef
  have hNZ : N ≤ center A := fun _ hc => hc.1
  have hN : N ≤ (QuotientGroup.mk' (center A)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hNZ
  set η : A ⧸ N →* A ⧸ center A := QuotientGroup.lift N (QuotientGroup.mk' (center A)) hN
  have hsurj : Function.Surjective η := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center A) q
    exact ⟨x, rfl⟩
  have hker : η.ker = (center A).map (QuotientGroup.mk' N) := by
    rw [QuotientGroup.ker_lift, QuotientGroup.ker_mk']
  have hperf : Group.IsPerfect (A ⧸ N) :=
    ⟨commutator_eq_top_of_surjective (QuotientGroup.mk'_surjective N) hA⟩
  refine ⟨A ⧸ N, inferInstance, inferInstance, hperf, η, hsurj, ?_, ?_, ?_⟩
  · rw [hker]
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hc g)]
  · rintro ⟨x, hx⟩
    rw [hker] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨a, ha⟩ := CFSG.LieType.Steinberg.exists_pow_two_pow_mem_oddPart (le_refl (center A)) hc
    refine ⟨a, Subtype.ext ?_⟩
    change (QuotientGroup.mk' N c) ^ 2 ^ a = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ha
  · intro hbot
    have hodd : ∀ c ∈ center A, Odd (orderOf c) := by
      intro c hc
      have hcN : QuotientGroup.mk' N c ∈ η.ker := by
        rw [hker]
        exact ⟨c, hc, rfl⟩
      rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcN
      exact hcN.2
    rcases Nat.even_or_odd (Nat.card (center A)) with h2 | h2
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨⟨c, hc⟩, hco⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp h2)
      have hco' : orderOf c = 2 := by
        rw [← hco, Subgroup.orderOf_mk]
      have := hodd c hc
      rw [hco'] at this
      exact absurd this (by decide)
    · exact h2

theorem odd_card_center_of_psl2 (hA : commutator A = ⊤) {m : ℕ} (hm : 3 ≤ m)
    (e : A ⧸ center A ≃* PSL(2, GaloisField 2 m)) : Odd (Nat.card (center A)) := by
  obtain ⟨E, _, _, _, η, hsurj, hcen, hp, hodd⟩ := exists_two_cover hA
  apply hodd
  have hcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  let e' := e.trans (CFSG.ShultStronglyClosedTI.glaSL2EquivNative m (by omega) hcard).symm
  let η' := e'.toMonoidHom.comp η
  have hker : η'.ker = η.ker := MonoidHom.ker_comp_of_injective η e'.toMonoidHom e'.injective
  have h := (CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_trivial m hm hcard η'
    (e'.surjective.comp hsurj) (hker.symm ▸ hcen) (hker.symm ▸ hp)).1
  rwa [hker] at h

theorem odd_card_center_of_psu3 (hA : commutator A = ⊤) {m : ℕ} (hm : 2 ≤ m)
    (e : A ⧸ center A ≃* PSU3 2 m) : Odd (Nat.card (center A)) := by
  obtain ⟨E, _, _, _, η, hsurj, hcen, hp, hodd⟩ := exists_two_cover hA
  apply hodd
  let η' := e.toMonoidHom.comp η
  have hker : η'.ker = η.ker := MonoidHom.ker_comp_of_injective η e.toMonoidHom e.injective
  have h := CFSG.ShultStronglyClosedTI.unitaryCover_native_kernel_eq_bot m hm η'
    (e.surjective.comp hsurj) (hker.symm ▸ hcen) (hker.symm ▸ hp)
  rwa [hker] at h


end Center

section Hyp

theorem hypII_of_nativeBenderType
    {A : Type} [Group A] [Finite A] (hA : commutator A = ⊤)
    (h : NativeBenderType (A ⧸ center A)) : AS76b.HypII A := by
  rcases h with ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact RankTwoBender.hypII_of_odd_center hA (odd_card_center_of_psl2 hA hm e)
      (RankTwoBender.hypII_of_bender (Or.inl ⟨m, by omega, ⟨e⟩⟩))
  · exact RankTwoBender.hypII_of_odd_center hA (odd_card_center_of_psu3 hA hm e)
      (RankTwoBender.hypII_of_bender (Or.inr (Or.inl ⟨m, hm, ⟨e⟩⟩)))
  · exact RankTwoBender.hypII_of_suzuki_cover RankTwoBender.suzukiInvolutoryInner hA ha e

variable {G : Type} [Group G] [Finite G]

theorem hyp31_of_standard
    {L : Subgroup G} (hstd : standardComponentIsStandard L)
    (hO : standardComponentOddCore G = ⊥) (hnn : ¬ L.Normal)
    (hrank : 2 ≤ Open.pRank 2 (centralizer (L : Set G)))
    (hB : RankTwoBenderType (rankTwoQuot L)) : AS76b.Hyp31 L :=
  ⟨hstd, hypII_of_nativeBenderType hstd.1.1 (rankTwoBenderType_iff.mp hB), hO, hrank, hnn⟩


end Hyp

end CFSG.ComponentClassification.GMS78
