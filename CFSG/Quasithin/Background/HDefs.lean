module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.D2Params
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.RankThree.Classical.SemilinearFixedBasis
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

namespace H

open CFSG.Open

variable {V : Type*} [CommGroup V]

@[expose] noncomputable def betaH (M : Subgroup (MulAut V)) : ℕ∞ :=
  ⨅ (U : Subgroup V) (_ : U ≠ ⊤) (_ : twoResidual (M ⊓ centSub U) ≠ ⊥), (rkIdx U : ℕ∞)

@[expose] def alphaSet [Finite V] (M : Subgroup (MulAut V)) : Set ℕ :=
  {k | 2 ≤ k ∧ ∃ U : Subgroup V, U ≠ ⊤ ∧ rkIdx U = k ∧
    k ≤ CFSG.Open.pRank 2 (M ⊓ centSub U) + 1}

open Classical in
@[expose] noncomputable def alphaH [Finite V] (M : Subgroup (MulAut V)) : ℕ :=
  if (alphaSet M).Nonempty then sInf (alphaSet M) else 1

@[expose] def IsFOneOffender (M A : Subgroup (MulAut V)) : Prop :=
  IsA2 M A ∧ rkIdx (fixV A) ≤ rk A + 1

@[expose] def IsFOneModule (M : Subgroup (MulAut V)) : Prop :=
  ∃ A : Subgroup (MulAut V), IsFOneOffender M A

@[expose] def HypBang (M : Subgroup (MulAut V)) : Prop :=
  ∃ (X : Type) (_ : Group X) (_ : Finite X), SQTKGroup X ∧
    ∃ φ : X →* ↥M, Function.Surjective φ

section Rank

variable {G : Type*} [Group G]

theorem isElemAbelian2_iff {A : Subgroup (MulAut V)} : IsElemAbelian2 A ↔ IsElemAbelian 2 A := by
  constructor
  · rintro ⟨hc, hs⟩
    exact ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, hs⟩
  · rintro ⟨hc, hs⟩
    refine ⟨fun a ha b hb => ?_, hs⟩
    have := @mul_comm' (↥A) _ hc ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this


theorem exists_isElemAbelian_card_pRank [Finite G] (H : Subgroup G) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ CFSG.Open.pRank 2 H :=
  CFSG.SectionRank.exists_pRank one_lt_two H

theorem exists_card_eq_two_pow_of_isElemAbelian [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : ∃ k : ℕ, Nat.card E = 2 ^ k := by
  have : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩
  exact (IsPGroup.iff_card (p := 2)).mp this

theorem card_le_two_pow_pRank [Finite G] {E H : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ CFSG.Open.pRank 2 H := by
  obtain ⟨k, hk⟩ := exists_card_eq_two_pow_of_isElemAbelian hE
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) (le_pRank Nat.prime_two hEH hE hk)


theorem rk_le_pRank [Finite V] {A H : Subgroup (MulAut V)} (hAH : A ≤ H)
    (hA : IsElemAbelian2 A) : rk ↥A ≤ CFSG.Open.pRank 2 H := by
  have : Finite (MulAut V) := MulEquiv.finite_left
  have hA' := isElemAbelian2_iff.mp hA
  obtain ⟨k, hk⟩ := exists_card_eq_two_pow_of_isElemAbelian hA'
  have : rk ↥A = k := by
    unfold rk
    rw [hk, padicValNat.prime_pow]
  rw [this]
  exact le_pRank Nat.prime_two hAH hA' hk

theorem pRank_two_map_of_injective [Finite G] {G' : Type*} [Group G'] [Finite G']
    (f : G →* G') (hf : Function.Injective f) (H : Subgroup G) :
    CFSG.Open.pRank 2 (H.map f) = CFSG.Open.pRank 2 H := by
  apply le_antisymm
  · obtain ⟨E, hEH, hE, hEc⟩ := exists_isElemAbelian_card_pRank (H.map f)
    have hEr : E ≤ f.range := hEH.trans (Subgroup.map_le_range f H)
    have hmc : (E.comap f).map f = E := Subgroup.map_comap_eq_self hEr
    have hcH : E.comap f ≤ H := by
      have := Subgroup.comap_mono (f := f) hEH
      rwa [Subgroup.comap_map_eq_self_of_injective hf] at this
    have hcard : Nat.card (E.comap f) = 2 ^ CFSG.Open.pRank 2 (H.map f) := by
      have := Nat.card_congr ((E.comap f).equivMapOfInjective f hf).toEquiv
      rw [hmc] at this
      exact this.trans hEc
    refine le_pRank Nat.prime_two hcH ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩ hcard
    · have := @mul_comm' (↥E) _ hE.1 ⟨f a, a.2⟩ ⟨f b, b.2⟩
      simpa using congrArg Subtype.val this
    · rw [map_pow, map_one]
      exact hE.2 _ hx
  · obtain ⟨E, hEH, hE, hEc⟩ := exists_isElemAbelian_card_pRank H
    refine le_pRank Nat.prime_two (Subgroup.map_mono hEH) ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩ ?_
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      apply Subtype.ext
      change f a' * f b' = f b' * f a'
      rw [← map_mul, ← map_mul]
      have := @mul_comm' (↥E) _ hE.1 ⟨a', ha'⟩ ⟨b', hb'⟩
      exact congrArg f (congrArg Subtype.val this)
    · obtain ⟨y, hy, rfl⟩ := hx
      rw [← map_pow, hE.2 y hy, map_one]
    · rw [← hEc]
      exact (Nat.card_congr (E.equivMapOfInjective f hf).toEquiv).symm

end Rank

theorem rkIdx_anti [Finite V] {U U' : Subgroup V} (h : U ≤ U') : rkIdx U' ≤ rkIdx U :=
  padicValNat_two_le_of_dvd Subgroup.index_ne_zero_of_finite (Subgroup.index_dvd_of_le h)

section Basic

variable {G : Type*} [Group G]

theorem twoResidual_eq_bot_iff [Finite G] {H : Subgroup G} :
    twoResidual H = ⊥ ↔ IsPGroup 2 H := by
  constructor
  · intro h x
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H x x.2
    rw [h, Subgroup.mem_bot] at hk
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · intro h
    refine le_bot_iff.mp (twoResidual_le_of_isTwoQuotient bot_le
      (fun g _ => Subgroup.mem_normalizer_iff.mpr fun x => ?_) fun y hy => ?_)
    · simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl
        simp
      · intro hx
        have := congrArg (fun z => g⁻¹ * z * g) hx
        simp only [mul_one, inv_mul_cancel] at this
        rw [← this]
        group
    · obtain ⟨k, hk⟩ := h ⟨y, hy⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end Basic

theorem le_betaH_iff {M : Subgroup (MulAut V)} {k : ℕ∞} :
    k ≤ betaH M ↔ ∀ U : Subgroup V, U ≠ ⊤ → twoResidual (M ⊓ centSub U) ≠ ⊥ →
      k ≤ (rkIdx U : ℕ∞) := by
  unfold betaH
  simp only [le_iInf_iff]

theorem le_betaH_iff_isPGroup [Finite V] {M : Subgroup (MulAut V)} {k : ℕ∞} :
    k ≤ betaH M ↔ ∀ U : Subgroup V, U ≠ ⊤ → ¬ IsPGroup 2 ↥(M ⊓ centSub U) →
      k ≤ (rkIdx U : ℕ∞) := by
  rw [le_betaH_iff]
  have : Finite (MulAut V) := MulEquiv.finite_left
  simp only [ne_eq, twoResidual_eq_bot_iff]

theorem alphaH_eq_one [Finite V] {M : Subgroup (MulAut V)} (h : alphaSet M = ∅) :
    alphaH M = 1 := by
  unfold alphaH
  rw [h]
  simp

theorem alphaH_eq_one_of_not_isFOneModule [Finite V] {M : Subgroup (MulAut V)}
    (hM : ¬ IsFOneModule M) : alphaH M = 1 := by
  apply alphaH_eq_one
  rw [Set.eq_empty_iff_forall_notMem]
  rintro k ⟨hk2, U, -, hUk, hkr⟩
  have : Finite (MulAut V) := MulEquiv.finite_left
  obtain ⟨A, hAle, hAel, hAcard⟩ := exists_isElemAbelian_card_pRank (M ⊓ centSub U)
  apply hM
  have hrkA : rk ↥A = CFSG.Open.pRank 2 (M ⊓ centSub U) := by
    unfold rk
    rw [hAcard, padicValNat.prime_pow]
  have hA1 : A ≠ ⊥ := by
    rintro rfl
    have h1 : rk ↥(⊥ : Subgroup (MulAut V)) = 0 := rk_bot
    omega
  have hfix : U ≤ fixV A := fun u hu a ha => (hAle ha).2 u hu
  refine ⟨A, ⟨hAle.trans inf_le_left, hA1, isElemAbelian2_iff.mpr hAel⟩, ?_⟩
  have hle : rkIdx (fixV A) ≤ rkIdx U := by
    unfold rkIdx
    exact padicValNat_two_le_of_dvd (Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hfix)
  omega

theorem mem_fixV_zpowers_iff {x : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers x) ↔ x v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply


end H

end CFSG.Quasithin
