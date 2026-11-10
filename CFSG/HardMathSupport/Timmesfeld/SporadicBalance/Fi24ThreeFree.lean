
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeFix

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native CFSG.Sporadic.FischerOddCore
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

section Defs

theorem cls_smul_J (s : J) (x : Fin 306936) : cls (s • x) = jR s * cls x * (jR s)⁻¹ := by
  rw [← CFSG.Sporadic.Fi24.jR_smul, CFSG.Sporadic.Fi24.cls_smul_R]

theorem InQ.smul {s : J} {x : Fin 306936} (h : InQ s x) : InQ s (s • x) := by
  unfold InQ at h ⊢
  rw [cls_smul_J s (s • x), cls_smul_J s x]
  calc jR s * cls x * (jR s)⁻¹ * (jR s * (jR s * cls x * (jR s)⁻¹) * (jR s)⁻¹)
      = jR s * (cls x * (jR s * cls x * (jR s)⁻¹)) * (jR s)⁻¹ := by group
    _ = jR s * (cls x * cls (s • x)) * (jR s)⁻¹ := by rw [cls_smul_J]
    _ = jR s * (cls (s • x) * cls x) * (jR s)⁻¹ := by rw [h]
    _ = jR s * (jR s * cls x * (jR s)⁻¹) * (jR s)⁻¹ * (jR s * cls x * (jR s)⁻¹) := by
        rw [cls_smul_J]; group

theorem InQ.comm3 {s : J} (hs : s ^ 3 = 1) {x : Fin 306936} (h : InQ s x) :
    cls (s • (s • x)) * cls x = cls x * cls (s • (s • x)) := by
  have h2 := h.smul.smul
  unfold InQ at h2
  have e : s • (s • (s • x)) = x := by
    rw [← mul_smul, ← mul_smul, ← pow_three', hs, one_smul]
  rw [e] at h2
  exact h2

theorem uR_smul {s : J} (hs : s ^ 3 = 1) {x : Fin 306936} (h : InQ s x) :
    uR s (s • x) = uR s x := by
  unfold uR
  have e : s • (s • (s • x)) = x := by
    rw [← mul_smul, ← mul_smul, ← pow_three', hs, one_smul]
  rw [e]
  have h1 : cls x * cls (s • x) = cls (s • x) * cls x := h
  have h2 : cls (s • x) * cls (s • (s • x)) = cls (s • (s • x)) * cls (s • x) := h.smul
  have h3 := h.comm3 hs
  calc cls (s • x) * cls (s • (s • x)) * cls x = cls (s • x) * (cls (s • (s • x)) * cls x) := by
        rw [mul_assoc]
    _ = cls (s • x) * (cls x * cls (s • (s • x))) := by rw [h3]
    _ = (cls (s • x) * cls x) * cls (s • (s • x)) := by rw [mul_assoc]
    _ = (cls x * cls (s • x)) * cls (s • (s • x)) := by rw [h1]

theorem uR_commute {s : J} (hs : s ^ 3 = 1) {x : Fin 306936} (h : InQ s x) :
    uR s x * jR s = jR s * uR s x := by
  have e : jR s * uR s x * (jR s)⁻¹ = uR s (s • x) := by
    unfold uR
    rw [cls_smul_J s (s • (s • x)), cls_smul_J s (s • x), cls_smul_J s x]
    group
  rw [uR_smul hs h] at e
  calc uR s x * jR s = jR s * uR s x * (jR s)⁻¹ * jR s := by rw [e]
    _ = jR s * uR s x := by group

theorem uR_mul_self {s : J} (hs : s ^ 3 = 1) {x : Fin 306936} (h : InQ s x) :
    uR s x * uR s x = 1 := by
  unfold uR
  have h1 : cls x * cls (s • x) = cls (s • x) * cls x := h
  have h2 : cls (s • x) * cls (s • (s • x)) = cls (s • (s • x)) * cls (s • x) := h.smul
  have h3 := h.comm3 hs
  set a := cls x
  set b := cls (s • x)
  set c := cls (s • (s • x))
  have ha : a * a = 1 := cls_mul_self _
  have hb : b * b = 1 := cls_mul_self _
  have hc : c * c = 1 := cls_mul_self _
  calc a * b * c * (a * b * c) = a * b * (c * a) * b * c := by group
    _ = a * b * (a * c) * b * c := by rw [h3]
    _ = a * (b * a) * c * b * c := by group
    _ = a * (a * b) * c * b * c := by rw [h1]
    _ = (a * a) * b * (c * b) * c := by group
    _ = (a * a) * b * (b * c) * c := by rw [h2]
    _ = (a * a) * (b * b) * (c * c) := by group
    _ = 1 := by rw [ha, hb, hc, one_mul, one_mul]

theorem conj_uR {s n : J} (hn : n * s = s * n) (x : Fin 306936) :
    jR n * uR s x * (jR n)⁻¹ = uR s (n • x) := by
  have hc : ∀ y : Fin 306936, n • (s • y) = s • (n • y) := fun y => by
    rw [← mul_smul, ← mul_smul, hn]
  unfold uR
  rw [← hc, ← hc]
  rw [← CFSG.Sporadic.Fi24.jR_smul n x, ← CFSG.Sporadic.Fi24.jR_smul n (s • x),
    ← CFSG.Sporadic.Fi24.jR_smul n (s • (s • x)), CFSG.Sporadic.Fi24.cls_smul_R,
    CFSG.Sporadic.Fi24.cls_smul_R, CFSG.Sporadic.Fi24.cls_smul_R]
  group

theorem InQ.of_commute {s n : J} (hn : n * s = s * n) {x : Fin 306936} (h : InQ s x) :
    InQ s (n • x) := by
  have hc : n • (s • x) = s • (n • x) := by rw [← mul_smul, ← mul_smul, hn]
  unfold InQ at h ⊢
  rw [← hc, ← CFSG.Sporadic.Fi24.jR_smul n x, ← CFSG.Sporadic.Fi24.jR_smul n (s • x),
    CFSG.Sporadic.Fi24.cls_smul_R, CFSG.Sporadic.Fi24.cls_smul_R]
  calc jR n * cls x * (jR n)⁻¹ * (jR n * cls (s • x) * (jR n)⁻¹)
      = jR n * (cls x * cls (s • x)) * (jR n)⁻¹ := by group
    _ = jR n * (cls (s • x) * cls x) * (jR n)⁻¹ := by rw [h]
    _ = jR n * cls (s • x) * (jR n)⁻¹ * (jR n * cls x * (jR n)⁻¹) := by group

end Defs

section Cycle


end Cycle

section Facts


end Facts

section Core

theorem smul_three {s : J} (hs : s ^ 3 = 1) (x : Fin 306936) : s • (s • (s • x)) = x := by
  rw [← mul_smul, ← mul_smul, ← pow_three', hs, one_smul]

theorem not_three_dvd_orderOf {N : Subgroup J} (hcop : Nat.Coprime 3 (Nat.card N)) {m : J}
    (hm : m ∈ N) : ¬ 3 ∣ orderOf m := by
  intro h3
  have hd : orderOf m ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨m, hm⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop (h3.trans hd)

theorem gLAPPrimeCoreOf_eq_bot_of_freeFacts {w : List ℕ} {d0 : Fin 306936} (hF : FreeFacts w d0) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({wordElt w} : Set J)) = ⊥ := by
  have := finite_J
  set s := wordElt w with hsdef
  set N := GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set J)) with hN
  have hcop : Nat.Coprime 3 (Nat.card N) := coprime_card_GLAPPrimeCoreOf Nat.prime_three _
  have hs3 : s ^ 3 = 1 := hF.pow3
  have hNs : ∀ n ∈ N, n * s = s * n := fun n hn =>
    CFSG.Sporadic.Fi24.mem_centralizer_J.1 (GLAPPrimeCoreOf_le _ hn)
  have hordR : ∀ m ∈ N, ¬ 3 ∣ orderOf (jR m) := fun m hm => by
    rw [orderOf_injective _ CFSG.Sporadic.Fi24.jR_injective]
    exact not_three_dvd_orderOf hcop hm
  have hu0 := uR_commute hs3 hF.qd0
  have hinv : ∀ {k : Fin 306936}, InQ s k → (uR s k)⁻¹ = uR s k := fun hk =>
    inv_eq_of_mul_eq_one_right (uR_mul_self hs3 hk)
  have step1 : ∀ n ∈ N, n • d0 = d0 ∨ n • d0 = s • d0 ∨ n • d0 = s • (s • d0) := by
    intro n hn
    by_contra hne
    push Not at hne
    obtain ⟨h1, h2, h3⟩ := hne
    set x := n • d0 with hx
    have hxQ : InQ s x := hF.qd0.of_commute (hNs n hn)
    obtain ⟨m1, hm1, e1⟩ := conj_mem_gLAPPrimeCoreOf hu0 hn
    have hw : uR s d0 * uR s x = jR (m1 * n⁻¹) := by
      rw [map_mul, e1, map_inv, hx, ← conj_uR (hNs n hn) d0, hinv hF.qd0]
      group
    have hwN : m1 * n⁻¹ ∈ N := N.mul_mem hm1 (N.inv_mem hn)
    have hsx := hxQ.smul
    have hssx := hsx.smul
    have hux1 : uR s (s • x) = uR s x := uR_smul hs3 hxQ
    have hux2 : uR s (s • (s • x)) = uR s x := by rw [uR_smul hs3 hsx, hux1]
    have hxx := smul_three hs3 x
    have hd := smul_three hs3 d0
    have hout : ∀ y : Fin 306936, (y = x ∨ y = s • x ∨ y = s • (s • x)) →
        y ≠ d0 ∧ y ≠ s • d0 ∧ y ≠ s • (s • d0) := by
      rintro y (rfl | rfl | rfl)
      · exact ⟨h1, h2, h3⟩
      · refine ⟨fun e => h3 ?_, fun e => h1 ?_, fun e => h2 ?_⟩
        · rw [← hxx, e]
        · rw [← hxx, e, hd]
        · rw [← hxx, e, hd]
      · refine ⟨fun e => h2 ?_, fun e => h3 ?_, fun e => h1 ?_⟩
        · rw [← hxx, e]
        · rw [← hxx, e]
        · rw [← hxx, e, hd]
    have hcrit : ∀ y : Fin 306936, (y = x ∨ y = s • x ∨ y = s • (s • x)) → InQ s y →
        uR s y = uR s x → y.val ≤ (s • y).val → y.val ≤ (s • (s • y)).val → False := by
      intro y hy hyQ hyu hy1 hy2
      obtain ⟨n1, n2, n3⟩ := hout y hy
      rcases hF.crit y hyQ n1 n2 n3 hy1 hy2 with hc | ⟨k, hk, hc⟩
      · rw [hyu, hw] at hc
        exact hordR _ hwN hc
      · rw [hyu, show uR s d0 * uR s x * uR s k * uR s d0 * uR s x * uR s k =
          (uR s d0 * uR s x) * (uR s k * (uR s d0 * uR s x) * (uR s k)⁻¹) by
            rw [hinv hk]; group, hw] at hc
        obtain ⟨m2, hm2, e2⟩ := conj_mem_gLAPPrimeCoreOf (uR_commute hs3 hk) hwN
        rw [← e2, ← map_mul] at hc
        exact hordR _ (N.mul_mem hwN hm2) hc
    by_cases c1 : x.val ≤ (s • x).val ∧ x.val ≤ (s • (s • x)).val
    · exact hcrit x (Or.inl rfl) hxQ rfl c1.1 c1.2
    · by_cases c2 : (s • x).val ≤ (s • (s • x)).val ∧ (s • x).val ≤ x.val
      · refine hcrit (s • x) (Or.inr (Or.inl rfl)) hsx hux1 c2.1 ?_
        rw [hxx]; exact c2.2
      · refine hcrit (s • (s • x)) (Or.inr (Or.inr rfl)) hssx hux2 ?_ ?_
        · rw [hxx]; omega
        · rw [smul_three hs3 (s • x)]; omega
  have step2 : ∀ n ∈ N, n • d0 = d0 := by
    intro n hn
    have hc : ∀ y : Fin 306936, n • (s • y) = s • (n • y) := fun y => by
      rw [← mul_smul, ← mul_smul, hNs n hn]
    rcases step1 n hn with h | h | h
    · exact h
    · exfalso
      apply not_three_dvd_orderOf hcop hn
      refine three_dvd_orderOf_of_smul_cycle n d0 (L := 3) (by norm_num) ?_ ?_
      · rw [pow_three, mul_smul, mul_smul, h, hc, h, hc, hc, h, smul_three hs3]
      · rw [Nat.div_self (by norm_num), pow_one, h]
        exact hF.fpf d0
    · exfalso
      apply not_three_dvd_orderOf hcop hn
      refine three_dvd_orderOf_of_smul_cycle n d0 (L := 3) (by norm_num) ?_ ?_
      · have e1 : n • (s • (s • d0)) = s • d0 := by
          rw [hc, hc, h, smul_three hs3 (s • d0)]
        have e2 : n • (s • d0) = d0 := by rw [hc, h, smul_three hs3]
        rw [pow_three, mul_smul, mul_smul, h, e1, e2]
      · rw [Nat.div_self (by norm_num), pow_one, h]
        intro e
        apply hF.fpf d0
        calc s • d0 = s • (s • (s • d0)) := by rw [e]
          _ = d0 := smul_three hs3 d0
  obtain ⟨H, hHs, hHQ⟩ := hF.orbit
  have step3 : ∀ n ∈ N, ∀ x : Fin 306936, InQ s x → n • x = x := by
    intro n hn x hx
    obtain ⟨g, hg, rfl⟩ := hHQ x hx
    have hgi : g⁻¹ * jR s = jR s * g⁻¹ := by
      have := hHs g hg
      calc g⁻¹ * jR s = g⁻¹ * (jR s * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * jR s) * g⁻¹ := by rw [this]
        _ = jR s * g⁻¹ := by group
    obtain ⟨m, hm, e⟩ := conj_mem_gLAPPrimeCoreOf hgi hn
    rw [← CFSG.Sporadic.Fi24.jR_smul, ← mul_smul,
      show jR n * g = g * (g⁻¹ * jR n * g⁻¹⁻¹) by group, ← e, mul_smul,
      CFSG.Sporadic.Fi24.jR_smul, step2 m hm]
  refine (Subgroup.eq_bot_iff_forall N).2 fun n hn => CFSG.Sporadic.Fi24.sep n fun t ht => ?_
  rw [CFSG.Sporadic.Fi24.chainBase_size] at ht
  obtain ⟨a, b, ha, hb, hab⟩ := hF.base t ht
  have hna : jR n * cls a = cls a * jR n := (smul_eq_iff_commute n a).1 (step3 n hn a ha)
  have hlt : chainBase[t]! < 306936 := by rw [← hab]; exact (cls a • b).2
  rw [idx_of_lt _ hlt]
  have e : (⟨chainBase[t]!, hlt⟩ : Fin 306936) = cls a • b := Fin.ext hab.symm
  rw [e, ← CFSG.Sporadic.Fi24.jR_smul, ← mul_smul, hna, mul_smul, CFSG.Sporadic.Fi24.jR_smul,
    step3 n hn b hb, hab]

end Core

section Outer

theorem exists_noncomm_cls_of_freeFacts {w : List ℕ} {d0 : Fin 306936} (hF : FreeFacts w d0)
    (k : Fin 306936) : ∃ t : J, t * wordElt w = wordElt w * t ∧ jR t * cls k ≠ cls k * jR t :=
  ⟨wordElt w, rfl, fun h => hF.fpf k ((smul_eq_iff_commute _ k).2 h)⟩

theorem uR_mul_uR_mem_JR (s : J) (k l : Fin 306936) : uR s k * uR s l ∈ JR := by
  unfold uR
  have e : cls k * cls (s • k) * cls (s • (s • k)) * (cls l * cls (s • l) * cls (s • (s • l))) =
      (cls k * cls (s • k)) * (cls (s • (s • k)) * cls l) * (cls (s • l) * cls (s • (s • l))) := by
    group
  rw [e]
  exact JR.mul_mem (JR.mul_mem (cls_mul_cls_mem_JR _ _) (cls_mul_cls_mem_JR _ _))
    (cls_mul_cls_mem_JR _ _)

theorem exists_noncomm_triple_of_freeFacts {w : List ℕ} {d0 : Fin 306936} (hF : FreeFacts w d0)
    {r : R} {K : Set (Fin 306936)} (hT : TripleOf r K) :
    ∃ t : J, t * wordElt w = wordElt w * t ∧ jR t * r ≠ r * jR t := by
  set s := wordElt w with hsdef
  have hs3 : s ^ 3 = 1 := hF.pow3
  by_contra hall
  push Not at hall
  have hperm : ∀ t : J, t * s = s * t → ∀ k ∈ K, jR t • k ∈ K := fun t ht k hk =>
    fo24_triple_perm hT.fix hT.comm hT.char (hall t ht) hk
  have hsK : ∀ k ∈ K, s • k ∈ K := fun k hk => by
    have := hperm s rfl k hk
    rwa [CFSG.Sporadic.Fi24.jR_smul] at this
  obtain ⟨k₁, k₂, k₃, hK⟩ := hT.three
  have hk : k₁ ∈ K := by rw [hK]; simp
  have hsk := hsK k₁ hk
  have hssk := hsK _ hsk
  have hQ : InQ s k₁ := hT.comm k₁ hk _ (hT.fix _ hsk)
  obtain ⟨a, b, ha, hb, hoff⟩ := hF.bgen
  obtain ⟨t, ht⟩ := exists_jR_of_mem (uR_mul_uR_mem_JR s a b)
  have hts : t * s = s * t := by
    apply CFSG.Sporadic.Fi24.jR_injective
    rw [map_mul, map_mul, ht, mul_assoc, uR_commute hs3 hb, ← mul_assoc, uR_commute hs3 ha,
      mul_assoc]
  have h1 := hperm t hts k₁ hk
  rw [ht] at h1
  obtain ⟨o1, o2, o3⟩ := hoff k₁ hQ
  have hne1 : k₁ ≠ s • k₁ := fun e => hF.fpf k₁ e.symm
  have hne2 : s • k₁ ≠ s • (s • k₁) := fun e => hF.fpf _ e.symm
  have hne3 : k₁ ≠ s • (s • k₁) := by
    intro e
    apply hF.fpf k₁
    calc s • k₁ = s • (s • (s • k₁)) := by rw [← e]
      _ = k₁ := smul_three hs3 k₁
  rw [hK] at hk hsk hssk h1
  rcases mem_of_three hk hsk hssk hne1 hne3 hne2 h1 with h | h | h
  · exact o1 h
  · exact o2 h
  · exact o3 h

end Outer

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
