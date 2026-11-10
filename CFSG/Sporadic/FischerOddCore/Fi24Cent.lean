module

public import CFSG.Sporadic.FischerOddCore.Fi24Free
public import CFSG.Sporadic.FischerOddCore.Fi24TabFacts
public import CFSG.Fischer.Polar.Facts

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native
open CFSG.Sporadic.Fi24 (R J M MR JR tR D24 jR cls)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open scoped commutatorElement

attribute [local instance] CFSG.Sporadic.Fi24.rAction


abbrev fi24L : Array Table := Fi24.letters

abbrev fi24TP : Table :=
  tPTable Fi24.orb (wordT nPts (letterJ fi24L) normWords[0]!)
    (wordT nPts (letterJ fi24L) normWords[1]!)


abbrev fi24D :
    R := fi23ToR CFSG.Sporadic.Fi23.d

abbrev fi24U2 :
    R := fi23ToR fi23U2

abbrev fi24U3 :
    R := fi23ToR fi23U3

theorem card_fixed_D24_pts (r : R) :
    Nat.card {x : D24 // r * x * r⁻¹ = x} = Nat.card {k : Fin 306936 // r • k = k} := by
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv Fi24.clsEquiv fun k => ?_)
  rw [Fi24.clsEquiv_apply, ← Fi24.cls_smul_R]
  exact ⟨fun h => by rw [h], fun h => Fi24.cls_injective h⟩

theorem rep_fi24TP :
    Rep 306936 fi24TP tR :=
  Fi24.rep_tR_of_tPOK Fi24.rep_nA Fi24.rep_nB
    (tPOK_tPTable _ _ _ fun p hp hpn => (Fi24.tree_facts p hpn hp).1)


theorem rep7_eq :
    rep7 0 = fi24D ∧ rep7 1 = fi24U2 ∧ rep7 2 = fi24U3 ∧ rep7 3 = tR ∧ rep7 4 = fi24D * tR ∧
      rep7 5 = fi24U2 * tR ∧ rep7 6 = fi24U3 * tR :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fi24_MR_class
    {m : R} (hm : m ∈ MR) (hm2 : m * m = 1) (hm1 : m ≠ 1) :
    ∃ r ∈ ({fi24D, fi24U2, fi24U3} : Set R), ∃ c ∈ MR, c * r * c⁻¹ = m := by
  obtain ⟨u, rfl⟩ := exists_fi23ToR hm
  have hu2 : u ^ 2 = 1 := fi23ToR_injective (by rw [map_pow, sq, hm2, map_one])
  have hu1 : u ≠ 1 := fun h => hm1 (by rw [h, map_one])
  have key : ∀ v : CFSG.Sporadic.Fi23.J, IsConj v u →
      ∃ c ∈ MR, c * fi23ToR v * c⁻¹ = fi23ToR u := fun v h => by
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact ⟨fi23ToR c, fi23ToR_mem c, by rw [← hc, map_mul, map_mul, map_inv]⟩
  rcases fi23_involution_class u hu2 hu1 with h | h | h
  · exact ⟨fi24D, Or.inl rfl, key _ h⟩
  · exact ⟨fi24U2, Or.inr (Or.inl rfl), key _ h⟩
  · exact ⟨fi24U3, Or.inr (Or.inr rfl), key _ h⟩

theorem fi24_involution_class
    {t : R} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ r ∈ ({fi24D, fi24U2, fi24U3, tR, fi24D * tR, fi24U2 * tR, fi24U3 * tR} : Set R),
      IsConj r t := by
  obtain ⟨x, hx, htx⟩ := Fi24.exists_commute_D24 CFSG.Fischer.polarFacts ht
  obtain ⟨g, hg⟩ := Fi24.exists_conj_eq_tR hx
  have hct : IsConj (jR g * t * (jR g)⁻¹) t := (isConj_iff.2 ⟨(jR g)⁻¹, by group⟩)
  have hT : jR g * t * (jR g)⁻¹ * tR = tR * (jR g * t * (jR g)⁻¹) := by
    rw [← hg]
    calc jR g * t * (jR g)⁻¹ * (jR g * x * (jR g)⁻¹) = jR g * (t * x) * (jR g)⁻¹ := by group
      _ = jR g * (x * t) * (jR g)⁻¹ := by rw [htx]
      _ = jR g * x * (jR g)⁻¹ * (jR g * t * (jR g)⁻¹) := by group
  set t' := jR g * t * (jR g)⁻¹ with ht'
  have ht'2 : t' * t' = 1 := by
    rw [ht', show jR g * t * (jR g)⁻¹ * (jR g * t * (jR g)⁻¹) = jR g * (t * t) * (jR g)⁻¹ by
      group, ht, mul_one, mul_inv_cancel]
  have ht'1 : t' ≠ 1 := fun h => ht1 (by
    rw [ht'] at h
    calc t = (jR g)⁻¹ * (jR g * t * (jR g)⁻¹) * jR g := by group
      _ = 1 := by rw [h]; group)
  rcases Fi24.mem_MR_or_of_commute (Subgroup.mem_centralizer_singleton_iff.2 hT) with hm | hm
  · obtain ⟨r, hr, c, -, hc⟩ := fi24_MR_class hm ht'2 ht'1
    refine ⟨r, ?_, ((isConj_iff (α := R)).2 ⟨c, hc⟩).trans hct⟩
    rcases hr with rfl | rfl | rfl <;> simp
  · have hmT := Fi24.commute_tR_of_mem_MR hm
    have hm2 : t' * tR * (t' * tR) = 1 := by
      calc t' * tR * (t' * tR) = t' * (tR * t') * tR := by group
        _ = t' * (t' * tR) * tR := by rw [hT]
        _ = t' * t' * (tR * tR) := by group
        _ = 1 := by rw [ht'2, Fi24.tR_mul_tR, mul_one]
    by_cases h1 : t' * tR = 1
    · refine ⟨tR, by simp, ?_⟩
      have : t' = tR := by
        calc t' = t' * tR * tR := by rw [mul_assoc, Fi24.tR_mul_tR, mul_one]
          _ = tR := by rw [h1, one_mul]
      exact this ▸ hct
    · obtain ⟨r, hr, c, hcM, hc⟩ := fi24_MR_class hm hm2 h1
      have hcT := Fi24.commute_tR_of_mem_MR hcM
      have e : c * (r * tR) * c⁻¹ = t' := by
        calc c * (r * tR) * c⁻¹ = c * r * c⁻¹ * (c * tR * c⁻¹) := by group
          _ = t' * tR * tR := by rw [hc, hcT, mul_inv_cancel_right]
          _ = t' := by rw [mul_assoc, Fi24.tR_mul_tR, mul_one]
      refine ⟨r * tR, ?_, ((isConj_iff (α := R)).2 ⟨c, e⟩).trans hct⟩
      rcases hr with rfl | rfl | rfl <;> simp


theorem fi24_oddCore_of_hard
    {r : R} (hr : orderOf r = 2) (hh : HardFacts r)
    (hq : Nat.gcd (Nat.card {x : D24 // r * x * r⁻¹ = x}) 2510411418381323442585600 ∣ 8 * 63 ∨
      Nat.gcd (Nat.card {x : D24 // r * x * r⁻¹ = x}) 2510411418381323442585600 ∣ 8 * 87) :
    CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set R)) = ⊥ := by
  obtain ⟨m, W, hW, hfix⟩ := hh
  exact fi24_oddCore_of_wit hr hq (k := 1) (fun _ => W) (fun _ => hW) (m := m) hfix

theorem orderOf_two_of
    {r : R} (h2 : r * r = 1) (h1 : r ≠ 1) : orderOf r = 2 :=
  orderOf_eq_prime (by rw [sq]; exact h2) h1

theorem fi24_inv_of_fi23
    {u : CFSG.Sporadic.Fi23.J} (hu : u ^ 2 = 1 ∧ u ≠ 1) :
    fi23ToR u * fi23ToR u = 1 ∧ fi23ToR u ≠ 1 :=
  ⟨by rw [← map_mul, ← sq, hu.1, map_one], fun h => hu.2 (fi23ToR_injective (by
    rw [h, map_one]))⟩

theorem fi24D_facts :
    fi24D * fi24D = 1 ∧ fi24D ≠ 1 :=
  fi24_inv_of_fi23 ⟨CFSG.Sporadic.Fi23.d_sq', fun h => by
    have := CFSG.Sporadic.Fi23.orderOf_d
    rw [h, orderOf_one] at this
    exact absurd this (by decide)⟩

theorem fi24U2_facts :
    fi24U2 * fi24U2 = 1 ∧ fi24U2 ≠ 1 := fi24_inv_of_fi23 fi23U2_facts

theorem fi24U3_facts :
    fi24U3 * fi24U3 = 1 ∧ fi24U3 ≠ 1 := fi24_inv_of_fi23 fi23U3_facts

theorem fi24_mul_tR_facts
    {m : R} (hm : m ∈ MR) (h2 : m * m = 1) :
    m * tR * (m * tR) = 1 ∧ m * tR ≠ 1 := by
  have hmT := Fi24.commute_tR_of_mem_MR hm
  refine ⟨?_, fun h => Fi24.tR_not_mem_MR ?_⟩
  · calc m * tR * (m * tR) = m * (tR * m) * tR := by group
      _ = m * (m * tR) * tR := by rw [hmT]
      _ = m * m * (tR * tR) := by group
      _ = 1 := by rw [h2, Fi24.tR_mul_tR, mul_one]
  · have : tR = m⁻¹ := by
      calc tR = m⁻¹ * (m * tR) := by group
        _ = m⁻¹ := by rw [h, mul_one]
    rw [this]
    exact Subgroup.inv_mem _ hm


theorem fi24_oddCore_reps :
    ∀ r ∈ ({fi24D, fi24U2, fi24U3, tR, fi24D * tR, fi24U2 * tR, fi24U3 * tR} : Set R),
      CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set R)) = ⊥ := by
  obtain ⟨hcnt, hh2, hh5, hh6⟩ := fi24Wit_facts
  have c : ∀ i < 7, Nat.card {x : D24 // rep7 i * x * (rep7 i)⁻¹ = x} =
      [3512, 3512, 504, 31672, 31672, 696, 696].getD i 0 := hcnt
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := rep7_eq
  have hM0 := fi23ToR_mem CFSG.Sporadic.Fi23.d
  have hM1 := fi23ToR_mem fi23U2
  have hM2 := fi23ToR_mem fi23U3
  have hT0 := fi24_mul_tR_facts hM0 fi24D_facts.1
  have hT1 := fi24_mul_tR_facts hM1 fi24U2_facts.1
  have hT2 := fi24_mul_tR_facts hM2 fi24U3_facts.1
  have c0 := c 0 (by norm_num)
  have c1 := c 1 (by norm_num)
  have c2 := c 2 (by norm_num)
  have c3 := c 3 (by norm_num)
  have c4 := c 4 (by norm_num)
  have c5 := c 5 (by norm_num)
  have c6 := c 6 (by norm_num)
  rw [e0] at c0
  rw [e1] at c1
  rw [e2] at c2 hh2
  rw [e3] at c3
  rw [e4] at c4
  rw [e5] at c5 hh5
  rw [e6] at c6 hh6
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fi24_oddCore_of_count (orderOf_two_of fi24D_facts.1 fi24D_facts.2)
      (by rw [c0]; norm_num)
  · exact fi24_oddCore_of_count (orderOf_two_of fi24U2_facts.1 fi24U2_facts.2)
      (by rw [c1]; norm_num)
  · exact fi24_oddCore_of_hard (orderOf_two_of fi24U3_facts.1 fi24U3_facts.2) hh2
      (Or.inl (by rw [c2]; norm_num))
  · exact fi24_oddCore_of_count Fi24.orderOf_tR (by rw [c3]; norm_num)
  · exact fi24_oddCore_of_count (orderOf_two_of hT0.1 hT0.2) (by rw [c4]; norm_num)
  · exact fi24_oddCore_of_hard (orderOf_two_of hT1.1 hT1.2) hh5 (Or.inr (by rw [c5]; norm_num))
  · exact fi24_oddCore_of_hard (orderOf_two_of hT2.1 hT2.2) hh6 (Or.inr (by rw [c6]; norm_num))

theorem CTUC_Fi24_all_extension_involution_centralizers_odd_core_trivial :
    ∀ t : R, orderOf t = 2 →
      CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set R)) = ⊥ ∧
        CFSG.oddCore ↥(JR ⊓ Subgroup.centralizer ({t} : Set R)) = ⊥ := by
  intro t ht
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by decide)
  obtain ⟨r, hr, hrt⟩ := fi24_involution_class ht2 ht1
  have hC := oddCore_centralizer_eq_bot_of_isConj hrt (fi24_oddCore_reps r hr)
  refine ⟨hC, oddCore_eq_bot_of_normal_le inf_le_right ?_ hC⟩
  refine ⟨fun n hn c => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnJ, hnc⟩ := Subgroup.mem_inf.1 hn
  exact Subgroup.mem_inf.2 ⟨Fi24.normal_JR.conj_mem _ hnJ _,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ c.2 hnc) (Subgroup.inv_mem _ c.2)⟩

end CFSG.Sporadic.FischerOddCore
