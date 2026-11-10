module

public import CFSG.Milestones.ASVolI.B1
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
public import CFSG.Quasithin.Background.S1549DGen
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Quasithin.Background.A4Bridge
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores
public import CFSG.Quasithin.Background.C124B2102

public section

namespace CFSG.ASVolI.ChB

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section B2Vocab

variable {G : Type*} [Group G]

@[expose] def Aj (H : Subgroup G) (j : ℕ) : Set (Subgroup G) :=
  {A | j ≤ CFSG.pRank 2 ↥H ∧
    ∃ A' ∈ CFSG.higherElemThompsonFamily ↥H j, A = A'.map H.subtype}

@[expose] noncomputable def Jj (H : Subgroup G) (j : ℕ) : Subgroup G :=
  if j ≤ CFSG.pRank 2 ↥H then
    (CFSG.higherElemThompson ↥H j).map H.subtype else ⊥

theorem Jj_eq_higherElemThompson_of_le (H : Subgroup G) (j : ℕ)
    (bound : j ≤ CFSG.pRank 2 ↥H) :
    Jj H j = (CFSG.higherElemThompson ↥H j).map H.subtype := by
  simp only [Jj, if_pos bound]


@[expose] def baumOf (H : Subgroup G) : Subgroup G :=
  H ⊓ Subgroup.centralizer (omegaOneCenterOf (Jj H 0) : Set G)

@[expose] def O2Phi (X : Subgroup G) : Subgroup G :=
  ((frattini (↥X ⧸ pCore 2 ↥X)).comap (QuotientGroup.mk' (pCore 2 ↥X))).map X.subtype

variable {V : Subgroup G}

@[expose] def starOffenders (hV : IsElemAbelian 2 V) (H : Subgroup G) :
    Set (Subgroup (MulAut (IntMod V hV))) :=
  {B | ∃ A ∈ Aj H 0, autI hV A ≠ ⊥ ∧ B = autI hV A}

@[expose] def starOffendersR (hV : IsElemAbelian 2 V) (R : Subgroup G) :
    Set (Subgroup (MulAut (IntMod V hV))) :=
  {B | ∃ A : Subgroup G, (∃ g : G, A.map (MulAut.conj g).toMonoidHom ∈ Aj R 0) ∧
    autI hV A ≠ ⊥ ∧ B = autI hV A}

@[expose] def IsFFOffenderRel (hV : IsElemAbelian 2 V) (H A : Subgroup G) : Prop :=
  A ∈ Aj H 0 ∧ autI hV A ≠ ⊥


@[expose] noncomputable def preimI (hV : IsElemAbelian 2 V) (Y : Subgroup (MulAut (IntMod V hV))) : Subgroup G :=
  (Y.comap (convI hV)).map (Subgroup.normalizer (V : Set G)).subtype

end B2Vocab

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

@[expose] def B_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (i : ℕ),
    ((Jj H i).subgroupOf H).Characteristic ∧ (IsPGroup 2 H → ((baumOf H).subgroupOf H).Characteristic)

section BurnsideB2a

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_pRank_eq {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    CFSG.pRank 2 ↥H = CFSG.Open.pRank 2 H :=
  CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank 2 H

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_le_pRank_of_corank {G : Type} [Group G] [Finite G] {H A : Subgroup G}
    {j : ℕ} (hA : CFSG.Quasithin.IsElemAbelianCorank H j A) : j ≤ CFSG.pRank 2 ↥H := by
  rw [burnsideB2a_pRank_eq H]
  have h1 : 2 ^ j ≤ 2 ^ CFSG.Open.pRank 2 H := by
    rw [← hA.2.2]
    exact Nat.le_mul_of_pos_left _ Nat.card_pos
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_corank_map {G : Type} [Group G] [Finite G] (H : Subgroup G) (j : ℕ)
    (hj : j ≤ CFSG.pRank 2 ↥H) (A' : Subgroup ↥H)
    (hA' : A' ∈ CFSG.higherElemThompsonFamily ↥H j) :
    CFSG.Quasithin.IsElemAbelianCorank H j (A'.map H.subtype) := by
  obtain ⟨hE, hc⟩ := (CFSG.mem_higherElemThompsonFamily_iff j A').1 hA'
  refine ⟨BlueprintB2.map_subtype_le_self A', ?_, ?_⟩
  · exact (BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mpr
      (BlueprintB2.isElementaryAbelian_map hE H.subtype)
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hc, ← burnsideB2a_pRank_eq H,
      ← pow_add, Nat.sub_add_cancel hj]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_family_of_corank {G : Type} [Group G] [Finite G] {H A : Subgroup G}
    {j : ℕ}
    (hA : CFSG.Quasithin.IsElemAbelianCorank H j A) :
    A.subgroupOf H ∈ CFSG.higherElemThompsonFamily ↥H j := by
  have hj : j ≤ CFSG.pRank 2 ↥H := burnsideB2a_le_pRank_of_corank hA
  refine (CFSG.mem_higherElemThompsonFamily_iff j (A.subgroupOf H)).2 ⟨?_, ?_⟩
  · exact BlueprintB2.isElementaryAbelian_subgroupOf
      ((BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mp hA.2.1)
  · rw [BlueprintB2.card_subgroupOf_eq hA.1]
    apply Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : (0 : ℕ) < 2) j)
    rw [hA.2.2, ← pow_add, Nat.sub_add_cancel hj, burnsideB2a_pRank_eq H]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_mem_Aj_iff {G : Type} [Group G] [Finite G] (H A : Subgroup G) (j : ℕ) :
    A ∈ Aj H j ↔ CFSG.Quasithin.IsElemAbelianCorank H j A := by
  unfold Aj
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hj, A', hA', rfl⟩
    exact burnsideB2a_corank_map H j hj A' hA'
  · intro hA
    exact ⟨burnsideB2a_le_pRank_of_corank hA, A.subgroupOf H,
      burnsideB2a_family_of_corank hA, (Subgroup.map_subgroupOf_eq_of_le hA.1).symm⟩


open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_Jj_zero {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    Jj H 0 = thompsonJ H := by
  rw [Jj_eq_higherElemThompson_of_le H 0 (Nat.zero_le _), CFSG.higherElemThompson_zero ↥H]
  exact elemThompson_map_subtype_eq_thompsonJ H


open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_mem_Aj_zero_iff {G : Type} [Group G] [Finite G] (H A : Subgroup G) :
    A ∈ Aj H 0 ↔ CFSG.Quasithin.IsMaxElemAbelian H A := by
  rw [burnsideB2a_mem_Aj_iff, CFSG.Quasithin.isMaxElemAbelian_iff_corank_zero]

private theorem burnsideB2a_card_eq_two_pow {W : Type} [Group W] [Finite W] (h : ∀ w : W, w ^ 2
    = 1) :
    ∃ k : ℕ, Nat.card W = 2 ^ k := by
  have hp : IsPGroup 2 W := by
    intro w
    exact ⟨1, by simpa using h w⟩
  exact IsPGroup.iff_card.mp hp

private theorem burnsideB2a_rk_eq {W : Type} [Group W] {k : ℕ} (hk : Nat.card W = 2 ^ k) :
    CFSG.Quasithin.rk W = k := by
  unfold CFSG.Quasithin.rk
  rw [hk, padicValNat.prime_pow]

private theorem burnsideB2a_index_eq_pow_rkIdx {W : Type} [Group W] [Finite W] {k : ℕ}
    (hk : Nat.card W = 2 ^ k) (H : Subgroup W) :
    H.index = 2 ^ CFSG.Quasithin.rkIdx H := by
  have hd : H.index ∣ 2 ^ k := by
    rw [← hk]
    exact H.index_dvd_card
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  unfold CFSG.Quasithin.rkIdx
  rw [hi, padicValNat.prime_pow]

end BurnsideB2a


@[expose] def B_2_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), IsPGroup 2 S →
    ∀ i j : ℕ, i ≤ j → j < CFSG.Open.pRank 2 S →
      Jj S i ≤ Jj S j ∧
      (omegaOneCenterOf (Jj S j) ≤ omegaOneOf (S ⊓ Subgroup.centralizer (Jj S i : Set G)) ∧
        omegaOneOf (S ⊓ Subgroup.centralizer (Jj S i : Set G)) = omegaOneCenterOf (Jj S i)) ∧
      (∀ R : Subgroup G, Jj S i ≤ R → R ≤ S → Jj S i = Jj R i) ∧
      (∀ R : Subgroup G, baumOf S ≤ R → R ≤ S → baumOf S = baumOf R) ∧
      (∀ U : Subgroup G, U ≤ S → IsElemAbelian 2 U → Jj S 0 ≤ S ⊓ Subgroup.centralizer (U : Set G) →
        baumOf S = baumOf (S ⊓ Subgroup.centralizer (U : Set G))) ∧
      (∀ A ∈ Aj S 0, A = omegaOneOf (S ⊓ Subgroup.centralizer (A : Set G))) ∧
      (omegaOneOf (S ⊓ Subgroup.centralizer (Jj S 0 : Set G)) = omegaOneCenterOf (Jj S 0) ∧
        omegaOneCenterOf (Jj S 0) = ⨅ (A : Subgroup G) (_ : A ∈ Aj S 0), A)


@[expose] def B_2_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (S : Subgroup G) (j : ℕ) (A : Subgroup G), IsPGroup 2 S → V ≤ S → A ∈ Aj S j →
      autI hV A ≠ ⊥ →
      (rkIdx (fixV (autI hV A)) ≤ rk (autI hV A) + j ∧
        (j = 0 → rAV (autI hV A) ≤ 1 ∧ IsFFModule (autI hV ⊤))) ∧
      (rkIdx (fixV (autI hV A)) = rk (autI hV A) + j →
        (((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) ∈ Aj S 0)) ∧
      (A ∈ Aj S 0 → rkIdx (fixV (autI hV A)) = rk (autI hV A) →
        ((((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) ∈ Aj S 0) ∧
          CFSG.Open.pRank 2 (S ⊓ Subgroup.centralizer (V : Set G)) = CFSG.Open.pRank 2 S ∧
          Aj (S ⊓ Subgroup.centralizer (V : Set G)) 0 ⊆ Aj S 0 ∧
          V ≤ omegaOneCenterOf (Jj (S ⊓ Subgroup.centralizer (V : Set G)) 0) ∧
          omegaOneCenterOf (Jj S 0) ≤ omegaOneCenterOf (Jj (S ⊓ Subgroup.centralizer (V : Set G)) 0)))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
theorem as_B_2_4 : B_2_4 := by
  intro G _ _ V hV _ S j A _ hVS hAS hA1
  have hcorank : CFSG.Quasithin.IsElemAbelianCorank S j A := (burnsideB2a_mem_Aj_iff S A j).1 hAS
  have hNtop : Subgroup.normalizer (V : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := by
    rw [hNtop]
    exact le_top
  have hm : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  have hmeq : (fixV (autI hV A)).index * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card V := by
    have h := Subgroup.card_mul_index (fixV (autI hV A))
    rw [card_fixV_autI hV hAN] at h
    rw [mul_comm]
    exact h
  have hbound := card_le_relIndex_mul_card_mul_two_pow hV hVS hcorank
  rw [← card_autI_eq hV hAN] at hbound
  have hsqA : ∀ w : ↥(autI hV A), w ^ 2 = 1 := fun w =>
    Subtype.ext ((isElemAbelian2_autI hV hcorank.2.1 hAN).2 w w.2)
  obtain ⟨ka, hka⟩ := burnsideB2a_card_eq_two_pow hsqA
  have hNa : Nat.card (autI hV A) = 2 ^ CFSG.Quasithin.rk (autI hV A) := by
    rw [burnsideB2a_rk_eq hka]
    exact hka
  obtain ⟨kW, hkW⟩ := burnsideB2a_card_eq_two_pow (W := IntMod V hV) (fun w => IntMod.sq_eq_one w)
  have hFindex : (fixV (autI hV A)).index = 2 ^ CFSG.Quasithin.rkIdx (fixV (autI hV A)) :=
    burnsideB2a_index_eq_pow_rkIdx hkW _
  have hle : CFSG.Quasithin.rkIdx (fixV (autI hV A)) ≤ CFSG.Quasithin.rk (autI hV A) + j := by
    have h1 : (fixV (autI hV A)).index ≤ Nat.card (autI hV A) * 2 ^ j := by
      refine Nat.le_of_mul_le_mul_right ?_ hm
      calc (fixV (autI hV A)).index * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))
          = Nat.card V := hmeq
        _ ≤ Nat.card (autI hV A) * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) * 2 ^ j :=
            hbound
        _ = Nat.card (autI hV A) * 2 ^ j * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
            ring
    rw [hFindex, hNa, ← pow_add] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hj0part : j = 0 → CFSG.Quasithin.rAV (autI hV A) ≤ 1 ∧ IsFFModule (autI hV ⊤) := by
    intro hj0
    subst hj0
    refine ⟨?_, ?_⟩
    · unfold CFSG.Quasithin.rAV
      apply div_le_one_of_le₀
      · have h0 : CFSG.Quasithin.rkIdx (fixV (autI hV A)) ≤ CFSG.Quasithin.rk (autI hV A) := by
          simpa using hle
        exact_mod_cast h0
      · positivity
    · exact isFFModule_autOn hV hVS (le_of_eq hNtop.symm) le_top
        ((burnsideB2a_mem_Aj_zero_iff S A).1 hAS)
        (fun h => hA1 ((autI_eq_bot_iff hV hAN).2 h))
  have h2 : CFSG.Quasithin.rkIdx (fixV (autI hV A)) = CFSG.Quasithin.rk (autI hV A) + j →
      ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) ∈ Aj S 0 := by
    intro heq
    have hx : (fixV (autI hV A)).index = Nat.card (autI hV A) * 2 ^ j := by
      rw [hFindex, hNa, heq, pow_add]
    have heq' : Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) * 2 ^ j := by
      rw [← card_autI_eq hV hAN, ← hmeq, hx]
      ring
    exact (burnsideB2a_mem_Aj_zero_iff S _).2 (isMaxElemAbelian_sup_of_eq hV hVS hcorank heq')
  have h3 : A ∈ Aj S 0 → CFSG.Quasithin.rkIdx (fixV (autI hV A)) = CFSG.Quasithin.rk (autI hV A) →
      (((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) ∈ Aj S 0 ∧
        CFSG.Open.pRank 2 (S ⊓ Subgroup.centralizer (V : Set G)) = CFSG.Open.pRank 2 S ∧
        Aj (S ⊓ Subgroup.centralizer (V : Set G)) 0 ⊆ Aj S 0 ∧
        V ≤ omegaOneCenterOf (Jj (S ⊓ Subgroup.centralizer (V : Set G)) 0) ∧
        omegaOneCenterOf (Jj S 0) ≤ omegaOneCenterOf (Jj (S ⊓ Subgroup.centralizer (V : Set G)) 0)) := by
    intro hA0 heq
    have hmax : CFSG.Quasithin.IsMaxElemAbelian S A := (burnsideB2a_mem_Aj_zero_iff S A).1 hA0
    have hx : (fixV (autI hV A)).index = Nat.card (autI hV A) := by
      rw [hFindex, hNa, heq]
    have heq' : Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
      rw [← card_autI_eq hV hAN, ← hmeq, hx]
    obtain ⟨hB, hpr, hsub, hV1, hV2⟩ := B24_three hV hVS hmax heq'
    refine ⟨(burnsideB2a_mem_Aj_zero_iff S _).2 hB, hpr, ?_, ?_, ?_⟩
    · intro A' hA'
      exact (burnsideB2a_mem_Aj_zero_iff S A').2
        (hsub A' ((burnsideB2a_mem_Aj_zero_iff _ A').1 hA'))
    · simp only [burnsideB2a_Jj_zero]
      exact hV1
    · simp only [burnsideB2a_Jj_zero]
      exact hV2
  exact ⟨⟨hle, hj0part⟩, h2, h3⟩

@[expose] def B_2_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal],
    (starOffenders hV ⊤ = ∅ ∨ IsStableFF (autI hV ⊤) (starOffenders hV ⊤)) ∧
      (∀ B ∈ starOffenders hV ⊤, IsFFStarOffender (autI hV ⊤) B) ∧
      (∀ B ∈ starOffenders hV ⊤, ∀ g ∈ autI hV ⊤,
        B.map (MulAut.conj g).toMonoidHom ∈ starOffenders hV ⊤) ∧
      (∀ A ∈ starOffenders hV ⊤, ∀ B : Subgroup (MulAut (IntMod V hV)),
        FFLe (autI hV ⊤) B A → B ∈ starOffenders hV ⊤)

section BurnsideB2b


end BurnsideB2b


@[expose] def B_2_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (A : Subgroup G), IsFFOffenderRel hV ⊤ A → IsFFStarOffender (autI hV ⊤) (autI hV A)


@[expose] def B_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (T : Subgroup G), IsSylowTwoOf T ⊤ →
      ((Jj ⊤ 0 ≤ Subgroup.centralizer (V : Set G) ∧
          (Subgroup.normalizer (Jj T 0 : Set G) : Set G) *
            (Subgroup.centralizer (V : Set G) : Set G) = Set.univ) ∨
        (¬ Jj ⊤ 0 ≤ Subgroup.centralizer (V : Set G) ∧ IsFFModule (autI hV ⊤) ∧
          IsStableFF (autI hV ⊤) (starOffenders hV ⊤))) ∧
      autI hV (Jj ⊤ 0) = ffJP (starOffenders hV ⊤) (autI hV ⊤) ∧
      ffJP (starOffenders hV ⊤) (autI hV ⊤) ≤ ffJ (autI hV ⊤)


@[expose] def B_2_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (A : Subgroup G), IsFFOffenderRel hV ⊤ A →
      (∀ B : Subgroup (MulAut (IntMod V hV)), FFLe (autI hV ⊤) B (autI hV A) →
        ∃ D ∈ Aj ⊤ 0, autI hV D = B ∧
          D = (A ⊓ preimI hV B) ⊔
            (V ⊓ Subgroup.centralizer ((A ⊓ preimI hV B) : Set G))) ∧
      (¬ IsStrongFFStarOffender (autI hV ⊤) (autI hV A) →
        rk (autI hV A) + rk (fixV (autI hV A)) = rk (IntMod V hV) ∧
        ∀ B : Subgroup (MulAut (IntMod V hV)), B ≠ ⊥ → B ≤ autI hV A → rAV B ≤ 1 →
          rk (IntMod V hV) ≤ rk B + rk (fixV B) ∧ FFLe (autI hV ⊤) B (autI hV A))


@[expose] def B_2_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (A : Subgroup G), IsFFOffenderRel hV ⊤ A →
      ¬ IsStrongFFStarOffender (autI hV ⊤) (autI hV A) →
      (∀ B : Subgroup (MulAut (IntMod V hV)), IsFFStarOffender (autI hV ⊤) B → B ≤ autI hV A →
        ∃ D : Subgroup G, IsFFOffenderRel hV ⊤ D ∧ autI hV D = B) ∧
      (∀ B : Subgroup (MulAut (IntMod V hV)), B ≠ ⊥ → B ≤ autI hV A → rAV B ≤ 1 →
        ∃ D : Subgroup G, IsFFOffenderRel hV ⊤ D ∧ autI hV D = B)


@[expose] def B_2_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (R T : Subgroup G), IsSylowTwoOf T ⊤ → pCoreOf 2 (⊤ : Subgroup G) ≤ R → R ≤ T →
      (pCoreOf 2 (⊤ : Subgroup G) = R ⊓ Subgroup.centralizer (V : Set G) →
        ((Jj R 0 = Jj (pCoreOf 2 (⊤ : Subgroup G)) 0 ∧
            baumOf R = baumOf (pCoreOf 2 (⊤ : Subgroup G)) ∧
            (Jj R 0).Normal ∧ (baumOf R).Normal) ∨
          (IsStableFF (autI hV ⊤) (starOffendersR hV R) ∧
            ffJP (starOffendersR hV R) (autI hV ⊤) ≤ ffJ (autI hV ⊤)))) ∧
      (pCoreOf 2 (autI hV ⊤) = ⊥ → ∀ L : Subgroup G,
        (L : Set G) * (T : Set G) = Set.univ → ¬ L ≤ Subgroup.centralizer (V : Set G) →
        ((quasithinIsCComponent L ⊤ ∧ CFSG.Open.IsQuasisimple (↥L ⧸ pCore 2 ↥L)) ∨
          Nonempty ((↥L ⧸ pCore 2 ↥L) ≃* Multiplicative (ZMod 3))) →
          IsSylowTwoOf (pCoreOf 2 (Subgroup.centralizer (V : Set G))) (Subgroup.centralizer (V : Set G)) ∧
          pCoreOf 2 (⊤ : Subgroup G) = R ⊓ Subgroup.centralizer (V : Set G) ∧
          autI hV L = quasithinGenFitting (autI hV ⊤) ∧
          (baumOf R = baumOf (pCoreOf 2 (⊤ : Subgroup G)) ∨
            autI hV L = quasithinGenFitting (ffJP (starOffendersR hV R) (autI hV ⊤))))

section BurnsideB2f


end BurnsideB2f


@[expose] def B_2_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G), V ∈ primeReducedFamily G 2 →
    pCoreOf 2 (⊤ : Subgroup G) ≤ Subgroup.centralizer (V : Set G) ∧
      V ≤ omegaOneCenterOf (pCoreOf 2 (⊤ : Subgroup G))

section BurnsideB2c


end BurnsideB2c


@[expose] def B_2_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ V₁ ∈ primeReducedFamily G 2, ∀ V₂ ∈ primeReducedFamily G 2,
      V₁ ⊔ V₂ ∈ primeReducedFamily G 2) ∧
    primeReducedAggregate G 2 ∈ primeReducedFamily G 2 ∧
    (∀ V ∈ primeReducedFamily G 2, V ≤ primeReducedAggregate G 2)


@[expose] def B_2_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSylowTwoOf T ⊤ →
    pCoreOf 2 (⊤ : Subgroup G) ≠ ⊥ → ∀ Z : Subgroup G, Z ≠ ⊥ →
      Z ≤ pCoreOf 2 (⊤ : Subgroup G) ⊓ omegaOneCenterOf T →
        Subgroup.normalClosure (Z : Set G) ∈ primeReducedFamily G 2 ∧
        ⁅Subgroup.normalClosure (Z : Set G), (⊤ : Subgroup G)⁆ ∈ primeReducedFamily G 2 ∧
        Subgroup.normalClosure (Z : Set G) =
          ⁅Subgroup.normalClosure (Z : Set G), (⊤ : Subgroup G)⁆ ⊔
            (Subgroup.normalClosure (Z : Set G) ⊓ Subgroup.center G)

section BurnsideB2d


end BurnsideB2d


@[expose] def B_2_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], genFittingFStar G = pCore 2 G →
    ∀ T : Subgroup G, IsSylowTwoOf T ⊤ → ∀ Z : Subgroup G, Z ≠ ⊥ → Z ≤ omegaOneCenterOf T →
      (Subgroup.normalClosure (Z : Set G) ∈ primeReducedFamily G 2 ∧
        ⁅Subgroup.normalClosure (Z : Set G), (⊤ : Subgroup G)⁆ ∈ primeReducedFamily G 2 ∧
        Subgroup.normalClosure (Z : Set G) =
          ⁅Subgroup.normalClosure (Z : Set G), (⊤ : Subgroup G)⁆ ⊔
            (Subgroup.normalClosure (Z : Set G) ⊓ Subgroup.center G)) ∧
      Subgroup.normalClosure (Z : Set G) ≤ omegaOneCenterOf (pCoreOf 2 (⊤ : Subgroup G)) ∧
      (pCore 2 (G ⧸ Subgroup.centralizer (Subgroup.normalClosure (Z : Set G) : Set G)) = ⊥ ∧
        pCore 2 (G ⧸ Subgroup.centralizer
          ((⁅Subgroup.normalClosure (Z : Set G), (⊤ : Subgroup G)⁆ : Subgroup G) : Set G)) = ⊥)


@[expose] def B_2_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], genFittingFStar G = pCore 2 G →
    ∀ T : Subgroup G, IsSylowTwoOf T ⊤ → ∀ Z : Subgroup G, Z = omegaOneCenterOf T →
      (¬ Jj T 0 ≤ Subgroup.centralizer (Subgroup.normalClosure (Z : Set G) : Set G) ∧
        (∃ hU : IsElemAbelian 2 (Subgroup.normalClosure (Z : Set G)),
          IsFFModule (autI hU ⊤) ∧ pCoreOf 2 (autI hU ⊤) = ⊥)) ∨
      (Jj T 0 ≤ Subgroup.centralizer (Subgroup.normalClosure (Z : Set G) : Set G) ∧
        (Subgroup.centralizer (Z : Set G) : Set G) * (Subgroup.normalizer (Jj T 0 : Set G) : Set G) =
          Set.univ)


@[expose] def B_2_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → genFittingFStar G = pCore 2 G →
    ∀ T : Subgroup G, IsSylowTwoOf T ⊤ → ∀ Z : Subgroup G, Z = omegaOneCenterOf T →
      ∀ V : Subgroup G, V = Subgroup.normalClosure (Z : Set G) →
        V ∈ primeReducedFamily G 2 ∧
        ((Jj T 0 ≤ Subgroup.centralizer (V : Set G) ∧
            (Subgroup.normalizer (Jj T 0 : Set G) : Set G) *
              (Subgroup.centralizer (omegaOneCenterOf T : Set G) : Set G) = Set.univ) ∨
          (¬ Jj T 0 ≤ Subgroup.centralizer (V : Set G) ∧ ∃ hV : IsElemAbelian 2 V,
            IsSylowTwoOf (autI hV (Jj T 0)) (autI hV (Jj ⊤ 0)) ∧
            ∃ (n : ℕ) (Ls : Fin n → Subgroup (MulAut (IntMod V hV))),
              IsIntDirProd (autI hV (Jj ⊤ 0)) Ls ∧
              IsIntDirSum (⊤ : Subgroup (IntMod V hV))
                (fun o : Option (Fin n) => o.elim (fixV (autI hV (Jj ⊤ 0))) (fun i => commV (Ls i))) ∧
              (∀ i, Nonempty (↥(Ls i) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∧
                ActsAsNaturalL2 (Ls i) (commV (Ls i))) ∧
              (∀ g ∈ autI hV ⊤, ∀ i, ∃ j, (Ls i).map (MulAut.conj g).toMonoidHom = Ls j ∧
                (commV (Ls i)).map g.toMonoidHom = commV (Ls j)))) ∧
        CFSG.Open.pRank 2 (T ⊓ Subgroup.centralizer (V : Set G)) = CFSG.Open.pRank 2 T ∧
        Jj (T ⊓ Subgroup.centralizer (V : Set G)) 0 ≤ Jj T 0

section BurnsideB2e


end BurnsideB2e


@[expose] def B_2_17 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (n : ℕ) (X : Fin n → Subgroup (MulAut V)) (L : Subgroup (MulAut V)),
      L ≤ ⨆ i, X i → ∑ i, rkIdx (fixV (X i)) ≤ rkIdx (fixV L) →
        fixV L = fixV (⨆ i, X i) ∧ rkIdx (fixV L) = ∑ i, rkIdx (fixV (X i))


@[expose] def B_2_18 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (R : Subgroup G), IsPGroup 2 R → V ≤ R →
      pCoreOf 2 (twoResidual (⊤ : Subgroup G)) ≤ R ⊓ Subgroup.centralizer (V : Set G) →
      twoResidual (⊤ : Subgroup G) ≤ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) →
      twoResidual (⊤ : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) ≤ O2Phi (twoResidual (⊤ : Subgroup G)) →
      (∀ B : Subgroup (MulAut (IntMod V hV)), B ≤ autI hV R →
        ¬ IsStrongFFStarOffender (autI hV ⊤) B) →
      ∀ (n : ℕ) (X : Fin n → Subgroup G),
        (∀ i, (∃ l ∈ twoResidual (⊤ : Subgroup G), (X i).map (MulAut.conj l).toMonoidHom ≤ R) ∧
          Jj (X i) 0 = X i ∧ CFSG.Open.pRank 2 (X i) = CFSG.Open.pRank 2 R) →
        autI hV (twoResidual (⊤ : Subgroup G)) ≤ ⨆ i, autI hV (X i) →
        ∑ i, rkIdx (fixV (autI hV (X i))) ≤ rkIdx (fixV (autI hV (twoResidual (⊤ : Subgroup G)))) →
        Jj R 0 ≤ ⨆ i, X i →
          pCoreOf 2 (twoResidual (⊤ : Subgroup G)) ≤ baumOf R ∧
          omegaOneCenterOf (Jj R 0) =
            (omegaOneCenterOf (Jj R 0) ⊓ Subgroup.centralizer (twoResidual (⊤ : Subgroup G) : Set G)) ⊔
              (V ⊓ Subgroup.centralizer (Jj R 0 : Set G)) ∧
          (IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
              ((twoResidual (⊤ : Subgroup G) ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) →
            IsSylowTwoOf (baumOf R ⊓ Subgroup.centralizer (V : Set G))
              ((twoResidual (⊤ : Subgroup G) ⊔ baumOf R) ⊓ Subgroup.centralizer (V : Set G)) ∧
            (IsSylowTwoOf (autI hV (baumOf R)) (autI hV (twoResidual (⊤ : Subgroup G)) ⊔ autI hV (baumOf R)) →
              IsSylowTwoOf (baumOf R) (twoResidual (⊤ : Subgroup G) ⊔ baumOf R)))


@[expose] def B_2_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (R : Subgroup G), IsPGroup 2 R → V ≤ R →
      pCoreOf 2 (twoResidual (⊤ : Subgroup G)) ≤ R ⊓ Subgroup.centralizer (V : Set G) →
      IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
        ((twoResidual (⊤ : Subgroup G) ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) →
      twoResidual (⊤ : Subgroup G) ≤ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) →
      twoResidual (⊤ : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) ≤ O2Phi (twoResidual (⊤ : Subgroup G)) →
      (∀ B : Subgroup (MulAut (IntMod V hV)), B ≤ autI hV R →
        ¬ IsStrongFFStarOffender (autI hV ⊤) B) →
      ∀ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod V hV))),
        (∀ i, (∃ l ∈ autI hV (twoResidual (⊤ : Subgroup G)), (Y i).map (MulAut.conj l).toMonoidHom ≤ autI hV R) ∧
          ∀ Ri : Subgroup G, IsSylowTwoOf Ri ((twoResidual (⊤ : Subgroup G) ⊔ R) ⊓ preimI hV (Y i)) →
            Y i = autI hV (Jj Ri 0) ∧ CFSG.Open.pRank 2 Ri = CFSG.Open.pRank 2 R) →
        autI hV (twoResidual (⊤ : Subgroup G)) ≤ ⨆ i, Y i →
        ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI hV (twoResidual (⊤ : Subgroup G)))) →
        (∀ B : Subgroup (MulAut (IntMod V hV)), B ≤ autI hV R → IsFFStarOffender (autI hV ⊤) B →
          ∃ (r : ℕ) (Bs : Fin r → Subgroup (MulAut (IntMod V hV))), B = ⨆ k, Bs k ∧
            ∀ k, IsFFStarOffender (autI hV ⊤) (Bs k) ∧
              ∃ (j : Fin n) (g : MulAut (IntMod V hV)), g ∈ autI hV (twoResidual (⊤ : Subgroup G)) ∧
                Bs k ≤ (Y j).map (MulAut.conj g).toMonoidHom ∧
                (Y j).map (MulAut.conj g).toMonoidHom ≤ autI hV R) →
          pCoreOf 2 (twoResidual (⊤ : Subgroup G)) ≤ baumOf R ∧
          omegaOneCenterOf (Jj R 0) =
            (omegaOneCenterOf (Jj R 0) ⊓ Subgroup.centralizer (twoResidual (⊤ : Subgroup G) : Set G)) ⊔
              (V ⊓ Subgroup.centralizer (Jj R 0 : Set G)) ∧
          IsSylowTwoOf (baumOf R ⊓ Subgroup.centralizer (V : Set G))
              ((baumOf R ⊔ twoResidual (⊤ : Subgroup G)) ⊓ Subgroup.centralizer (V : Set G)) ∧
          (IsSylowTwoOf (autI hV (baumOf R)) (autI hV (twoResidual (⊤ : Subgroup G)) ⊔ autI hV (baumOf R)) →
            IsSylowTwoOf (baumOf R) (twoResidual (⊤ : Subgroup G) ⊔ baumOf R))


@[expose] def B_2_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (R T : Subgroup G), IsSylowTwoOf T ⊤ → pCoreOf 2 (⊤ : Subgroup G) ≤ R → R ≤ T →
      ¬ Jj R 0 ≤ Subgroup.centralizer (V : Set G) →
      R ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (⊤ : Subgroup G) →
      ∀ Astar : Subgroup (MulAut (IntMod V hV)),
        IsFFStarOffender (autI hV R) Astar →
        (∀ B : Subgroup (MulAut (IntMod V hV)), IsFFStarOffender (autI hV R) B → B = Astar) →
        Astar = autI hV R ⊓ centSub (fixV Astar) →
          Astar = autI hV (Jj R 0) ∧ autI hV (Jj R 0) = autI hV (baumOf R)


@[expose] def B_2_21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal],
    Subgroup.centralizer (V : Set G) = V →
      ∀ A ∈ Aj ⊤ 0, (∃ a ∈ A, V ⊓ Subgroup.centralizer (A : Set G) = V ⊓ Subgroup.centralizer ({a} : Set G)) →
        A ∈ Aj ⊤ 0 ∧ ∀ B ∈ Aj ⊤ 0, autI hV B = autI hV A → B = A


end CFSG.ASVolI
