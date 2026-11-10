module

public import CFSG.GroupTheory.PCore.Defs
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup

section OddCoreFree

variable {Q : Type*} [Group Q] [Finite Q]

theorem card_le_two_of_normal_of_oddCore_eq_bot (hO : oddCore Q = ⊥) {C : Subgroup Q}
    (hC : C.Normal) (h2 : ∀ U : Subgroup Q, IsPGroup 2 U → U ≤ C → Nat.card U ≤ 2) :
    Nat.card C ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 C) := inferInstance
  have hScard : Nat.card S ≤ 2 := by
    rw [← card_map_of_injective C.subtype_injective]
    exact h2 _ (S.isPGroup'.map _) (map_subtype_le _)
  have hScyc : IsCyclic (S : Subgroup C) := by
    refine isCyclic_of_card_dvd_prime (p := 2) ?_
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    rw [hk] at hScard ⊢
    rcases k with _ | _ | k
    · exact one_dvd _
    · exact dvd_refl _
    · exfalso
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ, pow_succ] at hScard
      omega
  obtain ⟨-, -, -, ⟨-, hodd, hidx, -⟩, hchar⟩ := CFSG.cyclic_sylow_normal_odd_complement S hScyc
  have hKn : ((pPrimeCore 2 C).map C.subtype).Normal := by
    have := hC
    infer_instance
  have hKodd : Odd (Nat.card ((pPrimeCore 2 C).map C.subtype)) := by
    rwa [card_map_of_injective C.subtype_injective]
  have hKbot : (pPrimeCore 2 C).map C.subtype = ⊥ := by
    rw [eq_bot_iff, ← hO]
    exact le_sSup ⟨hKn, hKodd⟩
  have hK1 : Nat.card (pPrimeCore 2 C) = 1 := by
    rw [← card_map_of_injective C.subtype_injective, hKbot, card_bot]
  have hCS := (pPrimeCore 2 C).card_mul_index
  rw [hK1, hidx, one_mul] at hCS
  rw [← hCS]
  exact hScard

theorem le_center_of_normal_of_card_le_two {C : Subgroup Q} (hC : C.Normal)
    (h : Nat.card C ≤ 2) : C ≤ center Q := by
  intro c hc
  rw [mem_center_iff]
  intro q
  by_cases hc1 : c = 1
  · rw [hc1, mul_one, one_mul]
  have hcard : Nat.card C = 2 := by
    have h1 : 1 < Nat.card C := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact ⟨⟨⟨c, hc⟩, 1, fun h' => hc1 (congrArg Subtype.val h')⟩⟩
    omega
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : C)).1 hcard
  have hconj : q * c * q⁻¹ ∈ C := hC.conj_mem c hc q
  have e1 : (⟨c, hc⟩ : C) = y := huniq _ (fun h' => hc1 (congrArg Subtype.val h'))
  have e2 : (⟨q * c * q⁻¹, hconj⟩ : C) = y := huniq _ (by
    intro h'
    apply hc1
    have h'' : q * c * q⁻¹ = 1 := congrArg Subtype.val h'
    rw [mul_inv_eq_one] at h''
    simpa using h'')
  have e3 : q * c * q⁻¹ = c := congrArg Subtype.val (e2.trans e1.symm)
  rw [mul_inv_eq_iff_eq_mul] at e3
  exact e3

theorem centralizer_le_center_of_oddCore_eq_bot (hO : oddCore Q = ⊥) {E : Subgroup Q}
    (hE : E.Normal)
    (h2 : ∀ U : Subgroup Q, IsPGroup 2 U → U ≤ centralizer (E : Set Q) → Nat.card U ≤ 2) :
    centralizer (E : Set Q) ≤ center Q := by
  have hn : (centralizer (E : Set Q)).Normal := by
    have := hE
    infer_instance
  exact le_center_of_normal_of_card_le_two hn (card_le_two_of_normal_of_oddCore_eq_bot hO hn h2)

end OddCoreFree

section Quasisimple

private theorem isSimpleGroup_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) (hZ : center Q = ⊥) : IsSimpleGroup Q := by
  have := hQ.2
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

end Quasisimple

section Quotient

variable {H : Type*} [Group H] [Finite H]

private theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (oddCore X)) :=
  CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd

private theorem oddCore_quotient_eq_bot : oddCore (H ⧸ oddCore H) = ⊥ := by
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set N := (oddCore (H ⧸ oddCore H)).comap π with hN
  have hNn : N.Normal := (CFSG.oddCore_normal _).comap π
  have hidx : N.index = (oddCore (H ⧸ oddCore H)).index :=
    index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h1 := N.card_mul_index
  have h2 := (oddCore (H ⧸ oddCore H)).card_mul_index
  have h3 := card_eq_card_quotient_mul_card_subgroup (oddCore H)
  have hcard : Nat.card N = Nat.card (oddCore (H ⧸ oddCore H)) * Nat.card (oddCore H) := by
    have hidx0 : N.index ≠ 0 := index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx0)
    rw [h1, h3, ← h2, hidx]
    ring
  have hNodd : Odd (Nat.card N) := by
    rw [hcard]
    exact (odd_card_oddCore _).mul (odd_card_oddCore H)
  have hNle : N ≤ oddCore H := le_sSup ⟨hNn, hNodd⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (oddCore H) x
  rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hNle hx

omit [Finite H] in
private theorem mk_mem_centralizer_map_oddCore {t : H} {D : Subgroup H}
    (hDt : D ≤ centralizer ({t} : Set H)) :
    QuotientGroup.mk' (oddCore H) t ∈
      centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨d, hd, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 (hDt hd)]

theorem mk_mem_center_of_normal_map_oddCore {t : H} {D : Subgroup H}
    (hDt : D ≤ centralizer ({t} : Set H))
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) →
      Nat.card U ≤ 2)
    (hnorm : (D.map (QuotientGroup.mk' (oddCore H))).Normal) :
    QuotientGroup.mk' (oddCore H) t ∈ center (H ⧸ oddCore H) :=
  centralizer_le_center_of_oddCore_eq_bot oddCore_quotient_eq_bot hnorm hsyl
    (mk_mem_centralizer_map_oddCore hDt)

theorem centralizer_map_oddCore_eq_zpowers {t : H} (ht : orderOf t = 2) {D : Subgroup H}
    (hDt : D ≤ centralizer ({t} : Set H))
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) →
      Nat.card U ≤ 2)
    (hnorm : (D.map (QuotientGroup.mk' (oddCore H))).Normal) :
    centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) =
      zpowers (QuotientGroup.mk' (oddCore H) t) := by
  have hn : (centralizer (D.map (QuotientGroup.mk' (oddCore H)) :
      Set (H ⧸ oddCore H))).Normal := by
    have := hnorm
    infer_instance
  have hcard := card_le_two_of_normal_of_oddCore_eq_bot oddCore_quotient_eq_bot hn hsyl
  have hord : orderOf (QuotientGroup.mk' (oddCore H) t) = 2 := by
    refine orderOf_eq_prime (by rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]) ?_
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := (oddCore H).orderOf_dvd_natCard h1
    rw [ht] at h2
    exact (Nat.not_even_iff_odd.2 (odd_card_oddCore H)) (even_iff_two_dvd.2 h2)
  symm
  refine eq_of_le_of_card_ge (zpowers_le.2 (mk_mem_centralizer_map_oddCore hDt)) ?_
  rw [Nat.card_zpowers, hord]
  exact hcard


end Quotient

section Neighbour

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_normalizer_centralizer_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) : g ∈ normalizer (centralizer (X : Set G) : Set G) := by
  have hX : ∀ x, x ∈ X ↔ g * x * g⁻¹ ∈ X := mem_normalizer_iff.1 hg
  rw [mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : g⁻¹ * x * g ∈ X := by
      rw [hX]
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [e]
      exact hx
    have hcx := mem_centralizer_iff.1 hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcx]
      _ = g * c * g⁻¹ * x := by group
  · intro hc
    rw [mem_centralizer_iff]
    intro x hx
    have hcx := mem_centralizer_iff.1 hc _ ((hX x).1 hx)
    calc x * c = g⁻¹ * ((g * x * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * x * g⁻¹)) * g := by rw [hcx]
      _ = c * x := by group


end Neighbour

end CFSG.SeitzReduction.F4Pilot
