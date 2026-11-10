module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection8.theorem_8_1
import Mathlib.GroupTheory.NoncommCoprod

namespace CFSG
end CFSG
open CFSG

/-!
# Common complement-transfer tools for Huppert IV

This file contains the normal-complement, quotient, Thompson-subgroup, and
focal-transfer utilities used by Huppert IV.6.2 and later Huppert V arguments.
It deliberately avoids importing chapter V theorem files, so chapter IV remains
in book order.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v
/-- If a normal subgroup and its quotient are `p`-groups, then the ambient group is a `p`-group. -/
public theorem hkt_isPGroup_of_normal_quotient
    {p : ℕ} {G : Type u} [Group G] (N : Subgroup G) [N.Normal]
    (hN : IsPGroup p N) (hQ : IsPGroup p (G ⧸ N)) :
    IsPGroup p G := fun g => by
  rcases hQ (g : G ⧸ N) with ⟨k₁, hk₁⟩
  rw [← @QuotientGroup.mk_pow G _ N _ g (p ^ k₁), QuotientGroup.eq_one_iff] at hk₁
  rcases hN ⟨g ^ (p ^ k₁), hk₁⟩ with ⟨k₂, hk₂⟩
  use k₁ + k₂
  rw [SubmonoidClass.mk_pow, Subgroup.mk_eq_one, ← pow_mul, ← pow_add] at hk₂
  exact hk₂


/-- A finite nilpotent group is `p`-nilpotent for every prime `p`. -/
public theorem hkt_hasNormalPComplement_of_nilpotent
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hQ_nil : Group.IsNilpotent Q) : HasNormalPComplement p Q := by
  classical
  refine ⟨pPrimeCore p Q, inferInstance, pPrimeCore_coprime_card (p := p) (G := Q), ?_⟩
  have hquot_nil : Group.IsNilpotent (Q ⧸ pPrimeCore p Q) := by
    infer_instance
  have hcore_bot : pPrimeCore p (Q ⧸ pPrimeCore p Q) = ⊥ := by
    simpa using pPrimeCore_quotient_pPrimeCore_eq_bot (G := Q) (p := p)
  have htop_le :
      (⊤ : Subgroup (Q ⧸ pPrimeCore p Q)) ≤
        pCore p (Q ⧸ pPrimeCore p Q) ⊔ pPrimeCore p (Q ⧸ pPrimeCore p Q) := by
    have : Group.IsNilpotent (Q ⧸ pPrimeCore p Q) := hquot_nil
    have hnilTop : Group.IsNilpotent (↥(⊤ : Subgroup (Q ⧸ pPrimeCore p Q))) := by
      exact Group.nilpotent_of_mulEquiv
        (G := Q ⧸ pPrimeCore p Q) (G' := ↥(⊤ : Subgroup (Q ⧸ pPrimeCore p Q)))
        (Subgroup.topEquiv.symm :
          (Q ⧸ pPrimeCore p Q) ≃* ↥(⊤ : Subgroup (Q ⧸ pPrimeCore p Q)))
    have hTop_le_iSup :
        (⊤ : Subgroup (Q ⧸ pPrimeCore p Q)) ≤
          ⨆ q : (Nat.card (Q ⧸ pPrimeCore p Q)).primeFactors.attach,
            pCore q.1 (Q ⧸ pPrimeCore p Q) :=
      normal_nilpotent_le_sup_pCore
        (G := Q ⧸ pPrimeCore p Q)
        (N := (⊤ : Subgroup (Q ⧸ pPrimeCore p Q))) (hN := inferInstance) hnilTop
    refine hTop_le_iSup.trans ?_
    refine iSup_le ?_
    intro q
    by_cases hqp : q.1 = p
    · simp [hqp]
    · have hqprime : Nat.Prime q.1 := Nat.prime_of_mem_primeFactors q.1.2
      let : Fact (Nat.Prime q.1) := ⟨hqprime⟩
      obtain ⟨n, hn⟩ :=
        (pCore_isPGroup (G := Q ⧸ pPrimeCore p Q) (p := q.1)).exists_card_eq
      have hcop : Nat.Coprime p (Nat.card (pCore q.1 (Q ⧸ pPrimeCore p Q))) := by
        rw [hn]
        have hpq : p ≠ q.1 := by
          intro hpq'
          exact hqp hpq'.symm
        exact ((Nat.coprime_primes (Fact.out : Nat.Prime p) hqprime).2 hpq).pow_right n
      exact
        (le_sSup (show pCore q.1 (Q ⧸ pPrimeCore p Q) ∈
          {K : Subgroup (Q ⧸ pPrimeCore p Q) | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
            ⟨inferInstance, hcop⟩)).trans le_sup_right
  have htop_le_pcore :
      (⊤ : Subgroup (Q ⧸ pPrimeCore p Q)) ≤ pCore p (Q ⧸ pPrimeCore p Q) := by
    simpa [hcore_bot] using htop_le
  have htop_p : IsPGroup p (⊤ : Subgroup (Q ⧸ pPrimeCore p Q)) :=
    IsPGroup.to_le (H := (⊤ : Subgroup (Q ⧸ pPrimeCore p Q)))
      (K := pCore p (Q ⧸ pPrimeCore p Q))
      (pCore_isPGroup (G := Q ⧸ pPrimeCore p Q) (p := p)) htop_le_pcore
  simpa using htop_p.of_equiv
    (Subgroup.topEquiv : (⊤ : Subgroup (Q ⧸ pPrimeCore p Q)) ≃* (Q ⧸ pPrimeCore p Q))


public theorem hkt_isPGroup_quotient_map_subtype_of_extension
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) [H.Normal] (K : Subgroup H) [K.Characteristic]
    (hHKp : IsPGroup p (H ⧸ K)) (hGHp : IsPGroup p (G ⧸ H)) :
    IsPGroup p (G ⧸ K.map H.subtype) := by
  classical
  let N : Subgroup G := K.map H.subtype
  have hN_le_H : N ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨k, _hk, rfl⟩
    exact k.property
  have : N.Normal := by
    dsimp [N]
    infer_instance
  let qN : G →* G ⧸ N := QuotientGroup.mk' N
  let Hbar : Subgroup (G ⧸ N) := H.map qN
  have : Hbar.Normal := by
    exact Subgroup.Normal.map (inferInstance : H.Normal) qN (QuotientGroup.mk'_surjective N)
  have hHbar_p : IsPGroup p Hbar := by
    let eHN : H ⧸ N.subgroupOf H ≃* H ⧸ K :=
      QuotientGroup.quotientMulEquivOfEq (by
        simpa [N] using (subgroupOf_map_subtype_eq (K := H) K))
    let eRange : H ⧸ N.subgroupOf H ≃* Hbar := quotientSubgroupRangeEquiv H N
    exact hHKp.of_equiv (eHN.symm.trans eRange)
  have hquot_p : IsPGroup p ((G ⧸ N) ⧸ Hbar) := by
    let e : (G ⧸ N) ⧸ Hbar ≃* G ⧸ H :=
      QuotientGroup.quotientQuotientEquivQuotient (N := N) (M := H) hN_le_H
    exact hGHp.of_equiv e.symm
  obtain ⟨a, ha⟩ := hquot_p.exists_card_eq
  obtain ⟨b, hb⟩ := hHbar_p.exists_card_eq
  have hcard :
      Nat.card (G ⧸ N) = Nat.card ((G ⧸ N) ⧸ Hbar) * Nat.card Hbar := by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Hbar))
  refine IsPGroup.of_card (p := p) (G := G ⧸ N) (n := a + b) ?_
  rw [hcard, ha, hb, Nat.pow_add]

public theorem hkt_hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) [H.Normal]
    (hGHp : IsPGroup p (G ⧸ H))
    (hHcomp : HasNormalPComplement p H) :
    HasNormalPComplement p G := by
  classical
  let K : Subgroup H := pPrimeCore p H
  let N : Subgroup G := K.map H.subtype
  have : K.Characteristic := pPrimeCore_characteristic (p := p) (G := H)
  have hNnorm : N.Normal := by
    dsimp [N, K]
    infer_instance
  have hNcop : Nat.Coprime p (Nat.card N) := by
    have hcard : Nat.card N = Nat.card K := by
      simpa [N] using
        (Subgroup.card_map_of_injective (K := K) (f := H.subtype) H.subtype_injective)
    rw [hcard]
    exact pPrimeCore_coprime_card (G := H) (p := p)
  have hHKp : IsPGroup p (H ⧸ K) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p) (H := H) hHcomp
  have hGNp : IsPGroup p (G ⧸ N) :=
    hkt_isPGroup_quotient_map_subtype_of_extension (G := G) (p := p)
      H K hHKp hGHp
  exact ⟨N, hNnorm, hNcop, hGNp⟩


/-- A normal `p`-complement descends to an arbitrary normal quotient.  The image
of the original `p'`-complement is still of `p'`-order, and the new quotient is a
surjective image of the old `p`-group quotient. -/
public theorem hkt_hasNormalPComplement_to_quotient
    {H : Type u} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (N : Subgroup H) [N.Normal] :
    HasNormalPComplement p H → HasNormalPComplement p (H ⧸ N) := by
  classical
  intro hcomp
  rcases hcomp with ⟨K, hKnorm, hKcop, hquotp⟩
  let qN : H →* H ⧸ N := QuotientGroup.mk' N
  let Kbar : Subgroup (H ⧸ N) := K.map qN
  have hKbar_norm : Kbar.Normal :=
    Subgroup.Normal.map hKnorm qN (QuotientGroup.mk'_surjective N)
  have hKbar_cop : Nat.Coprime p (Nat.card Kbar) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := K) qN) hKcop
  let φ0 : H →* (H ⧸ N) ⧸ Kbar := (QuotientGroup.mk' Kbar).comp qN
  have hK_le_ker : K ≤ φ0.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (N := Kbar) (x := qN x)).2
      (Subgroup.mem_map_of_mem qN hx)
  let φ : H ⧸ K →* (H ⧸ N) ⧸ Kbar := QuotientGroup.lift K φ0 hK_le_ker
  have hφ_surj : Function.Surjective φ :=
    QuotientGroup.lift_surjective_of_surjective
      (N := K) (φ := φ0) (by
        intro y
        obtain ⟨y0, rfl⟩ := QuotientGroup.mk'_surjective Kbar y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y0
        exact ⟨x, rfl⟩) hK_le_ker
  exact ⟨Kbar, hKbar_norm, hKbar_cop, hquotp.of_surjective φ hφ_surj⟩

/-- A normal `p`-complement for a subgroup descends to its image in a quotient by
an ambient normal subgroup contained in it. -/
public theorem hkt_hasNormalPComplement_map_quotient_of_normal_subgroup
    {H : Type u} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (N K : Subgroup H) [N.Normal] (_hN_le_K : N ≤ K)
    [hN_K_normal : (N.subgroupOf K).Normal]
    (hcomp : HasNormalPComplement p K) :
    HasNormalPComplement p (K.map (QuotientGroup.mk' N)) := by
  classical
  have hquot : HasNormalPComplement p (K ⧸ N.subgroupOf K) := by
    exact hkt_hasNormalPComplement_to_quotient (H := K) (p := p)
      (N := N.subgroupOf K) hcomp
  let e : K ⧸ N.subgroupOf K ≃* K.map (QuotientGroup.mk' N) :=
    quotientSubgroupRangeEquiv K N
  exact hasNormalPComplement_of_equiv (G := K ⧸ N.subgroupOf K) (p := p) e hquot
/-- For a quotient by a normal subgroup already contained in `T`, normalizers
commute with passing to the quotient. -/
public theorem hkt_normalizer_map_quotient_eq_map_normalizer_of_le
    {G : Type u} [Group G] (N T : Subgroup G) [N.Normal] (hN_le_T : N ≤ T) :
    let q : G →* G ⧸ N := QuotientGroup.mk' N
    Subgroup.normalizer (T.map q : Set (G ⧸ N)) =
      (Subgroup.normalizer (T : Set G)).map q := by
  classical
  intro q
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective N
  apply Subgroup.comap_injective hqsurj
  rw [Subgroup.comap_normalizer_eq_of_surjective (H := T.map q) hqsurj]
  rw [QuotientGroup.comap_map_mk' (N := N) (H := T)]
  rw [QuotientGroup.comap_map_mk' (N := N) (H := Subgroup.normalizer (T : Set G))]
  have hN_le_norm : N ≤ Subgroup.normalizer (T : Set G) :=
    hN_le_T.trans (Subgroup.le_normalizer (H := T))
  rw [sup_eq_right.mpr hN_le_T, sup_eq_right.mpr hN_le_norm]


/-- If `N ≤ T`, a normal `p`-complement for `N_G(T)` descends to the image of
`N_G(T)` in `G/N`. -/
public theorem hkt_hasNormalPComplement_normalizer_map_quotient_of_le
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N T : Subgroup G) [N.Normal] (hN_le_T : N ≤ T)
    (hcomp : HasNormalPComplement p (Subgroup.normalizer (T : Set G))) :
    let q : G →* G ⧸ N := QuotientGroup.mk' N
    HasNormalPComplement p ((Subgroup.normalizer (T : Set G)).map q) := by
  classical
  intro q
  have hN_le_norm : N ≤ Subgroup.normalizer (T : Set G) :=
    hN_le_T.trans (Subgroup.le_normalizer (H := T))
  have : (N.subgroupOf (Subgroup.normalizer (T : Set G))).Normal := by
    have hnorm_top : Subgroup.normalizer (N : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr (inferInstance : N.Normal)
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := N) (K := Subgroup.normalizer (T : Set G)) hN_le_norm).2 (by
          simp [hnorm_top])
  exact hkt_hasNormalPComplement_map_quotient_of_normal_subgroup
    (H := G) (p := p) (N := N) (K := Subgroup.normalizer (T : Set G))
    hN_le_norm hcomp


/-- If `N ≤ T`, then a normal `p`-complement for the ambient normalizer of `T`
gives one for the normalizer of `T/N` in the quotient. -/
public theorem hkt_hasNormalPComplement_normalizer_map_quotient_of_normalizer
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N T : Subgroup G) [N.Normal] (hN_le_T : N ≤ T)
    (hcomp : HasNormalPComplement p (Subgroup.normalizer (T : Set G))) :
    let q : G →* G ⧸ N := QuotientGroup.mk' N
    HasNormalPComplement p
      (Subgroup.normalizer (T.map q : Set (G ⧸ N))) := by
  classical
  intro q
  have hcomp_map : HasNormalPComplement p ((Subgroup.normalizer (T : Set G)).map q) := by
    simpa [q] using
      hkt_hasNormalPComplement_normalizer_map_quotient_of_le
        (G := G) (p := p) (N := N) (T := T) hN_le_T hcomp
  rw [hkt_normalizer_map_quotient_eq_map_normalizer_of_le
    (G := G) (N := N) (T := T) hN_le_T]
  exact hcomp_map


/-- If a quotient is a `p`-group, the image of any Sylow `p`-subgroup in that
quotient is all of the quotient. -/
public theorem sylow_map_quotient_eq_top_of_quotient_isPGroup
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N : Subgroup G) [N.Normal]
    (hquot : IsPGroup p (G ⧸ N)) :
    (S : Subgroup G).map (QuotientGroup.mk' N) = ⊤ := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Q := G ⧸ N
  let Tmap : Sylow p Q := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have htop_p : IsPGroup p (⊤ : Subgroup Q) := by
    simpa [Q] using hquot.to_subgroup (⊤ : Subgroup (G ⧸ N))
  let Ttop : Sylow p Q :=
    IsPGroup.toSylow (G := Q) (p := p) htop_p (by
      simpa using (Fact.out : Nat.Prime p).not_dvd_one)
  have hTtop_normal : (Ttop : Subgroup Q).Normal := by
    have hTtop_eq : (Ttop : Subgroup Q) = ⊤ := by
      dsimp [Ttop]
    rw [hTtop_eq]
    infer_instance
  have : Unique (Sylow p Q) := Sylow.unique_of_normal Ttop hTtop_normal
  have hSylow_eq : Tmap = Ttop := Subsingleton.elim _ _
  change (Tmap : Subgroup Q) = ⊤
  simpa [Tmap, Ttop, IsPGroup.toSylow_coe, q, Q] using
    congrArg (fun P : Sylow p Q => (P : Subgroup Q)) hSylow_eq

/-- Element form of `sylow_map_quotient_eq_top_of_quotient_isPGroup`: every
quotient class has a representative in the fixed Sylow subgroup. -/
public theorem hkt_exists_sylow_div_mem_of_quotient_isPGroup
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N : Subgroup G) [N.Normal]
    (hquot : IsPGroup p (G ⧸ N)) (g : G) :
    ∃ s : G, s ∈ (S : Subgroup G) ∧ g * s⁻¹ ∈ N := by
  classical
  have hmap_top :
      (S : Subgroup G).map (QuotientGroup.mk' N) = ⊤ :=
    sylow_map_quotient_eq_top_of_quotient_isPGroup
      (G := G) (p := p) S N hquot
  have hgmap : QuotientGroup.mk' N g ∈ (S : Subgroup G).map (QuotientGroup.mk' N) := by
    simp [hmap_top]
  rcases Subgroup.mem_map.mp hgmap with ⟨s, hsS, hs_eq⟩
  refine ⟨s, hsS, ?_⟩
  have hdiv : g / s ∈ N :=
    (QuotientGroup.eq_iff_div_mem (N := N)).1 hs_eq.symm
  simpa [div_eq_mul_inv] using hdiv


/-- If the canonical `p'`-core has vanished, the canonical quotient criterion
is just `Q` itself being a `p`-group. -/
public theorem hkt_isPGroup_of_quotient_pPrimeCore_isPGroup_of_pPrimeCore_eq_bot
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hcore : pPrimeCore p Q = ⊥)
    (hquot : IsPGroup p (Q ⧸ pPrimeCore p Q)) :
    IsPGroup p Q := by
  let e : Q ⧸ pPrimeCore p Q ≃* Q ⧸ (⊥ : Subgroup Q) :=
    QuotientGroup.quotientMulEquivOfEq hcore
  have hbot : IsPGroup p (Q ⧸ (⊥ : Subgroup Q)) := hquot.of_equiv e
  exact hbot.of_equiv (QuotientGroup.quotientBot (G := Q))

public theorem hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hcore : pPrimeCore p Q = ⊥) (hcomp : HasNormalPComplement p Q) :
    IsPGroup p Q :=
  hkt_isPGroup_of_quotient_pPrimeCore_isPGroup_of_pPrimeCore_eq_bot
    (Q := Q) (p := p) hcore
    (isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
      (p := p) (H := Q) hcomp)


/-- If `p` does not divide the group order, the whole group is a normal
`p`-complement and the quotient is trivial. -/
public theorem hkt_hasNormalPComplement_of_not_dvd_card
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hnot : ¬ p ∣ Nat.card Q) : HasNormalPComplement p Q := by
  classical
  refine ⟨⊤, inferInstance, ?_, ?_⟩
  · simpa using (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hnot
  · have : Subsingleton (Q ⧸ (⊤ : Subgroup Q)) :=
      QuotientGroup.subsingleton_quotient_top
    refine IsPGroup.of_card (p := p) (G := Q ⧸ (⊤ : Subgroup Q)) (n := 0) ?_
    simp

/--
Burnside's normal-complement endpoint in the precise form needed as the easy
branch of Thompson IV.6.2: if the Sylow subgroup already centralizes its
normalizer, then the desired normal `q`-complement follows without using the
Thompson local hypotheses.
-/
public theorem hkt_hasNormalPComplement_of_sylow_le_center_normalizer
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q)
    (hS : (S : Subgroup Q) ≤ centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q))) :
    HasNormalPComplement q Q := by
  exact hasNormalPComplement_of_sylow_le_center_normalizer (G := Q) q S hS

/-- If a top subgroup has a normal `p`-complement, transport it to the ambient
group. -/
public theorem hkt_hasNormalPComplement_of_subgroup_eq_top
    {Q : Type u} [Group Q] {q : ℕ} (H : Subgroup Q)
    (hHtop : H = ⊤) (hH : HasNormalPComplement q H) :
    HasNormalPComplement q Q := by
  let e : H ≃* Q :=
    (MulEquiv.subgroupCongr hHtop).trans
      (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
  exact hasNormalPComplement_of_equiv (G := H) (p := q) e hH


/-- The transfer map to the focal quotient is already onto when restricted to a
Sylow subgroup: on the focal quotient the restriction is the `index`-power map,
and the Sylow index is prime to `q`. -/
public theorem hkt_transferFocal_restrict_surjective
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) :
    Function.Surjective
      (((S : Subgroup Q).feitThompsonTransferFocal).domRestrict (S : Subgroup Q)) := by
  classical
  let H : Subgroup Q := S
  intro y
  have hquot_p : IsPGroup q (H ⧸ H.feitThompsonFocalSubgroupOf) := by
    simpa [H] using S.2.to_quotient ((S : Subgroup Q).feitThompsonFocalSubgroupOf)
  have hindex : ¬ q ∣ H.index := by
    simpa [H] using S.not_dvd_index
  obtain ⟨z, hz⟩ := (hquot_p.powEquiv' hindex).surjective y
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective H.feitThompsonFocalSubgroupOf z
  refine ⟨s, ?_⟩
  rw [MonoidHom.domRestrict_apply, Subgroup.feitThompsonTransferFocal_eq_pow]
  exact hz


end External
end CFSG.BenderSuzuki
