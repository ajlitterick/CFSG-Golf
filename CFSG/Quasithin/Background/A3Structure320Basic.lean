module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.Quasithin

namespace A320

open CFSG.Open CFSG.SectionRank
open scoped commutatorElement

theorem pRank_add_le {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hN : ¬ p ∣ Nat.card N) {X E : Subgroup G}
    (hX : IsElemAbelian p X) (hE : IsElemAbelian p E)
    (hcomm : ∀ x ∈ X, ∀ e ∈ E, ⁅x, e⁆ ∈ N)
    (hinj : ∀ x ∈ X, ∀ e ∈ E, x * e ∈ N → x = 1 ∧ e = 1)
    {a b : ℕ} (hXa : Nat.card X = p ^ a) (hEb : Nat.card E = p ^ b) :
    a + b ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  have hcomm' : ∀ (x : X) (e : E), QuotientGroup.mk' N (x : G) * QuotientGroup.mk' N (e : G) =
      QuotientGroup.mk' N (e : G) * QuotientGroup.mk' N (x : G) := by
    intro x e
    have h1 : QuotientGroup.mk' N ⁅(x : G), (e : G)⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hcomm x x.2 e e.2)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  let f : ↥X × ↥E →* G ⧸ N :=
    { toFun := fun u => QuotientGroup.mk' N (u.1 : G) * QuotientGroup.mk' N (u.2 : G)
      map_one' := by simp
      map_mul' := by
        intro u v
        have h := hcomm' v.1 u.2
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul, mul_assoc]
        rw [← mul_assoc (QuotientGroup.mk' N (v.1 : G)), h, mul_assoc] }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : QuotientGroup.mk' N ((u.1 : G) * (u.2 : G)) = 1 := by
      simpa [f, map_mul] using hu
    obtain ⟨h2, h3⟩ := hinj u.1 u.1.2 u.2 u.2.2 ((QuotientGroup.eq_one_iff _).1 h1)
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  have hbound : a + b ≤ CFSG.Open.pRank p (⊤ : Subgroup (G ⧸ N)) := by
    have := hX.1
    have := hE.1
    refine le_pRank_of_injective hp.out.one_lt (A := ↥X × ↥E) ?_ ?_ ?_ f hf le_top
    · intro u v
      exact Prod.ext (mul_comm' u.1 v.1) (mul_comm' u.2 v.2)
    · intro u
      exact Prod.ext (Subtype.ext (hX.2 _ u.1.2)) (Subtype.ext (hE.2 _ u.2.2))
    · rw [Nat.card_prod, hXa, hEb, pow_add]
  rwa [pRank_quotient_eq N hN] at hbound

theorem exists_orderOf_eq_three_not_mem {L : Type*} [Group L] [Finite L]
    (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤) {Z : Subgroup L}
    (hZc : Z ≤ Subgroup.center L) (hZ : Nat.card Z = 3) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by simpa using hZ)
  obtain ⟨P, hZP⟩ := hZp.exists_le_sylow
  have hZP' : Z ≤ (P : Subgroup L) := hZP
  have hnt : Nontrivial Z := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨z, hz⟩ := exists_ne (1 : Z)
  have hz3 : (z : L) ^ 3 = 1 := by
    have := pow_card_eq_one' (x := z)
    rw [hZ] at this
    exact congrArg Subtype.val this
  have hz1 : (z : L) ≠ 1 := fun h => hz (Subtype.ext h)
  have hzc : (z : L) ∈ Subgroup.center L := hZc z.2
  let ϕ : ↥(P : Subgroup L) →* Abelianization ↥(P : Subgroup L) := Abelianization.of
  have hkey : ∀ (k : ℕ) (g₀ : L), g₀⁻¹ * (z : L) ^ k * g₀ ∈ (P : Subgroup L) →
      g₀⁻¹ * (z : L) ^ k * g₀ = (z : L) ^ k := by
    intro k g₀ _
    have h1 := Subgroup.mem_center_iff.1 ((Subgroup.center L).pow_mem hzc k) g₀
    rw [mul_assoc, ← h1, ← mul_assoc, inv_mul_cancel, one_mul]
  have hzi : (z : L) ^ (P : Subgroup L).index ∈ (P : Subgroup L) :=
    MonoidHom.transfer_eq_pow_aux (z : L) hkey
  have htr := MonoidHom.transfer_eq_pow ϕ (z : L) hkey
  have hT1 : MonoidHom.transfer ϕ (z : L) = 1 := by
    have hle := Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ)
    have hcom : commutator L = ⊤ := by rw [commutator_def]; exact hperf
    exact hle (hcom ▸ Subgroup.mem_top (z : L))
  rw [htr] at hT1
  have hmem : (⟨(z : L) ^ (P : Subgroup L).index, hzi⟩ : ↥(P : Subgroup L)) ∈
      commutator ↥(P : Subgroup L) := by
    rw [← Abelianization.ker_of]
    exact hT1
  let z' : ↥(P : Subgroup L) := ⟨z, hZP' z.2⟩
  have hz'3 : z' ^ 3 = 1 := Subtype.ext hz3
  have hidx : ¬ 3 ∣ (P : Subgroup L).index := P.not_dvd_index
  have hpow : ∀ n : ℕ, z' ^ n = z' ^ (n % 3) := fun n => by
    calc z' ^ n = z' ^ (3 * (n / 3) + n % 3) := by rw [Nat.div_add_mod]
      _ = z' ^ (n % 3) := by rw [pow_add, pow_mul, hz'3, one_pow, one_mul]
  have hz'mem : z' ∈ commutator ↥(P : Subgroup L) := by
    have h1 : z' ^ (P : Subgroup L).index ∈ commutator ↥(P : Subgroup L) := hmem
    have h2 : (P : Subgroup L).index % 3 = 1 ∨ (P : Subgroup L).index % 3 = 2 := by omega
    rw [hpow] at h1
    rcases h2 with h2 | h2
    · rwa [h2, pow_one] at h1
    · rw [h2] at h1
      have h3 : z' = (z' ^ 2)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ']
        exact hz'3
      rw [h3]
      exact Subgroup.inv_mem _ h1
  have hncyc : ¬ IsCyclic ↥(P : Subgroup L) := by
    intro hcyc
    have hbot : commutator ↥(P : Subgroup L) = ⊥ := by
      rw [commutator_eq_bot_iff]
      infer_instance
    rw [hbot, Subgroup.mem_bot] at hz'mem
    exact hz1 (congrArg Subtype.val hz'mem)
  have : Fact (IsPGroup 3 ↥(P : Subgroup L)) := ⟨P.isPGroup'⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (R := ↥(P : Subgroup L)) (p := 3)
    (by norm_num) hncyc
  have hZcard' : Nat.card (Z.subgroupOf (P : Subgroup L)) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP').toEquiv).trans hZ
  obtain ⟨s, hsS, hsZ⟩ : ∃ s ∈ S, s ∉ Z.subgroupOf (P : Subgroup L) := by
    by_contra hcon
    push Not at hcon
    have hle : S ≤ Z.subgroupOf (P : Subgroup L) := hcon
    have := Subgroup.card_le_of_le hle
    rw [hScard, hZcard'] at this
    omega
  have : CFSG.IsElementaryAbelian 3 ↥S := hSel
  have hs3 : s ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian s hsS
  have hsZ' : (s : L) ∉ Z := fun h => hsZ (Subgroup.mem_subgroupOf.2 h)
  refine ⟨(s : L), ?_, hsZ'⟩
  have hs1 : (s : L) ≠ 1 := fun h => hsZ' (h ▸ Z.one_mem)
  exact orderOf_eq_prime (congrArg Subtype.val hs3 : (s : L) ^ 3 = 1) hs1


theorem pRank_le_pRank_map {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) (f : G →* G') (hf : IsPGroup q f.ker)
    (H : Subgroup G) : CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (H.map f) := by
  obtain ⟨E, hEH, hE, hcard⟩ := exists_pRank hp.out.one_lt H
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hdisj : Disjoint E f.ker := IsPGroup.disjoint_of_ne p q hpq E f.ker hEp hf
  have hinj : Function.Injective (f.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : G) ∈ f.ker := hx
    exact Subtype.ext (Subgroup.disjoint_def.1 hdisj x.2 h1)
  have := hE.1
  refine le_pRank_of_injective hp.out.one_lt (A := ↥E) (fun a b => mul_comm' a b)
    (fun a => Subtype.ext (hE.2 a a.2)) hcard (f.comp E.subtype) hinj ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨x, hEH x.2, rfl⟩

theorem exists_subgroup_card_prime {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {H : Subgroup G} (h : 1 ≤ CFSG.Open.pRank p H) :
    ∃ X : Subgroup G, X ≤ H ∧ IsElemAbelian p X ∧ Nat.card X = p := by
  obtain ⟨E, hEH, hE, hcard⟩ := exists_pRank hp.out.one_lt H
  have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by
    rw [hcard]
    exact Nat.one_lt_pow (by omega) hp.out.one_lt)
  obtain ⟨x, hx⟩ := exists_ne (1 : E)
  have hx1 : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
  have hxp : (x : G) ^ p = 1 := hE.2 x x.2
  refine ⟨Subgroup.zpowers (x : G), (Subgroup.zpowers_le.2 x.2).trans hEH, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro y ⟨n, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  · rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]

theorem eq_one_of_pow_eq_one_of_not_dvd {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]
    {R : Subgroup G} (hR : ¬ p ∣ Nat.card R) {e : G} (he : e ∈ R) (hep : e ^ p = 1) : e = 1 := by
  have h1 : orderOf e ∣ p := orderOf_dvd_of_pow_eq_one hep
  have h2 : orderOf e ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R he
  rcases (Nat.dvd_prime hp.out).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ h2) hR

end A320

end CFSG.Quasithin
