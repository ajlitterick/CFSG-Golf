module

public import CFSG.RankThree.PartTwo.Sec21.UniqueFixedPoint
public import CFSG.Foundations.Basic
public import CFSG.Assembly.InCatalog
public import CFSG.Open.FusionDefs
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridge
import CFSG.StronglyEmbedded.BenderNormalSeries
import CFSG.Adapters.Involutions
import CFSG.LinearAlgebra.LinearGroups.CyclicSylowIndexTwo

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Open


@[expose] def HoltUniqueFixedPointSimple : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ∀ N : Subgroup X, N ≠ ⊤ → ∀ z : X, orderOf z = 2 →
      (∃ S : Sylow 2 X, z ∈ (S : Subgroup X) ∧ (S : Subgroup X) ≤ Subgroup.centralizer {z}) →
      (∃! q : X ⧸ N, z • q = q) →
      (∃ M : Subgroup X, CFSG.IsStronglyEmbedded M) ∨
        ∃ n : ℕ, Odd n ∧ Nonempty (X ≃* alternatingGroup (Fin n))

section Simple

variable {G : Type*} [Group G]

theorem pPrimeCore_two_eq_bot_of_simple [Finite G] [IsSimpleGroup G] {z : G}
    (hz : orderOf z = 2) : CFSG.pPrimeCore 2 G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.pPrimeCore 2 G).Normal := CFSG.pPrimeCore_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pPrimeCore 2 G) with h | h
  · exact h
  · exfalso
    have hcop := CFSG.pPrimeCore_coprime_card (p := 2) (G := G)
    rw [h, Subgroup.card_top] at hcop
    have h2 : 2 ∣ Nat.card G := hz ▸ orderOf_dvd_natCard z
    rw [Nat.Coprime, Nat.gcd_eq_left h2] at hcop
    exact absurd hcop (by norm_num)

theorem center_eq_bot_of_simple [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have hb : b ∈ Subgroup.center G := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem faithfulSMul_quotient_of_simple [IsSimpleGroup G] {K : Subgroup G} (hK : K ≠ ⊤) :
    FaithfulSMul G (G ⧸ K) := by
  have hcore : K.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K.normalCore with h | h
    · exact h
    · exact absurd (eq_top_iff.mpr (h ▸ K.normalCore_le)) hK
  refine ⟨fun {g₁ g₂} h => ?_⟩
  have hker : g₂⁻¹ * g₁ ∈ (MulAction.toPermHom G (G ⧸ K)).ker := by
    rw [MonoidHom.mem_ker]
    ext q
    change (g₂⁻¹ * g₁) • q = q
    rw [mul_smul, h q, inv_smul_smul]
  rw [← Subgroup.normalCore_eq_ker, hcore, Subgroup.mem_bot, inv_mul_eq_one] at hker
  exact hker.symm


end Simple

section Catalog

variable {G : Type} [Group G]

theorem fusionIsBenderGroup_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : fusionIsBenderGroup X) : fusionIsBenderGroup Y := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.symm.trans e'⟩⟩)

theorem inCatalog_of_isStronglyEmbedded [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {M : Subgroup G} (hM : CFSG.IsStronglyEmbedded M)
    {z : G} (hz : orderOf z = 2) {S : Sylow 2 G} (hzS : z ∈ (S : Subgroup G)) :
    CFSG.Assembly.InCatalog G := by
  have hcenter := center_eq_bot_of_simple hnonab
  have h2 : 2 ∣ Nat.card G := hz ▸ orderOf_dvd_natCard z
  rcases bender_strongly_embedded_normal_series G M hM with hlow |
    ⟨M', N', hM', hN', hMN, -, hodd, hidx, hB⟩
  · exfalso
    rcases hlow S with hS | ⟨r, hr, ⟨e⟩⟩
    · classical
      let : Fintype G := Fintype.ofFinite G
      have heven : Even (Fintype.card G) := by
        rw [← Nat.card_eq_fintype_card]
        exact even_iff_two_dvd.mpr h2
      obtain ⟨-, -, hnorm, hidx2⟩ := CFSG.LinearGroups.cyclic_sylow_index_two heven S hS
      have key : ∀ H : Subgroup G, H.Normal → H.index = 2 → False := by
        intro H hH hH2
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
        · rw [h, Subgroup.index_bot] at hH2
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          have : IsCyclic G := isCyclic_of_prime_card hH2
          obtain ⟨a, b, hab⟩ := hnonab
          exact hab (mul_comm' a b)
        · rw [h, Subgroup.index_top] at hH2
          exact absurd hH2 (by norm_num)
      exact key _ hnorm hidx2
    · obtain ⟨hne, hcen⟩ := CFSG.Adapters.brauer_suzuki r hr S ⟨e⟩ z hzS hz
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
      · have hzc : z ∈ Subgroup.center G := by
          rw [Subgroup.mem_center_iff]
          intro g
          have hg := Subgroup.mem_center_iff.mp hcen (g : G ⧸ CFSG.oddCore G)
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, h,
            Subgroup.mem_bot, inv_mul_eq_one] at hg
          exact hg
        rw [hcenter, Subgroup.mem_bot] at hzc
        rw [hzc, orderOf_one] at hz
        exact absurd hz (by norm_num)
      · exact hne ((QuotientGroup.eq_one_iff z).mpr (h ▸ Subgroup.mem_top z))
  · have hM'bot : M' = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M' with h | h
      · exact h
      · exfalso
        rw [h, Subgroup.card_top] at hodd
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    have hN'top : N' = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N' with h | h
      · exfalso
        rw [h, Subgroup.index_bot] at hidx
        exact (Nat.not_even_iff_odd.mpr hidx) (even_iff_two_dvd.mpr h2)
      · exact h
    subst hM'bot hN'top
    have e : (⊤ : Subgroup G) ⧸ (⊥ : Subgroup G).subgroupOf ⊤ ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf ⊤)).trans
        (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
    exact CFSG.QuasithinUnique.inCatalog_of_fusionIsBenderGroup hnonab
      (fusionIsBenderGroup_of_mulEquiv e hB)


theorem inCatalog_of_mulEquiv_alternating_odd (hnonab : ∃ a b : G, a * b ≠ b * a) {n : ℕ}
    (hn : Odd n) (e : G ≃* alternatingGroup (Fin n)) : CFSG.Assembly.InCatalog G := by
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    have hn13 : n = 1 ∨ n = 3 := by
      obtain ⟨k, rfl⟩ := hn
      omega
    rcases hn13 with rfl | rfl
    · exact Subsingleton.elim _ _
    · have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card hcard
      exact mul_comm' _ _
  · exact ⟨.alternating n h5, ⟨e⟩⟩

theorem inCatalog_of_unique_fixed (hHolt : HoltUniqueFixedPointSimple) [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {N : Subgroup G} (hN : N ≠ ⊤) {z : G}
    (hz : orderOf z = 2) (hfix : ∀ q : G ⧸ N, z • q = q ↔ q = ((1 : G) : G ⧸ N))
    (hT : ∃ T : Sylow 2 N, z ∈ (T : Subgroup N).map N.subtype ∧
      (T : Subgroup N).map N.subtype ≤ Subgroup.centralizer {z}) :
    CFSG.Assembly.InCatalog G := by
  obtain ⟨S, hzS, hSc⟩ := exists_sylow_two_two_central hz hfix hT
  rcases hHolt G hnonab N hN z hz ⟨S, hzS, hSc⟩
      ⟨((1 : G) : G ⧸ N), (hfix _).mpr rfl, fun q hq => (hfix q).mp hq⟩ with
    ⟨M, hM⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact inCatalog_of_isStronglyEmbedded hnonab hM hz hzS
  · exact inCatalog_of_mulEquiv_alternating_odd hnonab hn e

end Catalog

end CFSG.RankThree.PartTwo.Sec21
