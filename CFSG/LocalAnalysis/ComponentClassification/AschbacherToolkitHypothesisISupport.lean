module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.Adapters.Involutions
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitCentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupShapes

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open CFSG.Open
open scoped Pointwise

section Restrict

variable {G : Type*} [Group G]

@[expose] def restrictAut (α : MulAut G) (H : Subgroup G) (hH : H.map (α : G →* G) = H) :
    MulAut H :=
  (α.subgroupMap H).trans (MulEquiv.subgroupCongr hH)

theorem restrictAut_apply (α : MulAut G) (H : Subgroup G) (hH : H.map (α : G →* G) = H)
    (h : H) : ((restrictAut α H hH h : H) : G) = α h :=
  rfl

theorem restrictAut_sq (α : MulAut G) (hα : α ^ 2 = 1) (H : Subgroup G)
    (hH : H.map (α : G →* G) = H) : restrictAut α H hH ^ 2 = 1 := by
  ext h
  rw [sq, MulAut.mul_apply, restrictAut_apply, restrictAut_apply, ← MulAut.mul_apply, ← sq, hα]
  rfl

theorem quotient_congr_sq (α : MulAut G) (hα : α ^ 2 = 1) (N : Subgroup G) [N.Normal]
    (hN : N.map (α : G →* G) = N) : QuotientGroup.congr N N α hN ^ 2 = 1 := by
  ext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [sq, MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, ← MulAut.mul_apply,
    ← sq, hα]
  rfl

theorem exists_invariant_sylow_two [Finite G] (α : MulAut G) (hα : α ^ 2 = 1) :
    ∃ P : Sylow 2 G, (P : Subgroup G).map (α : G →* G) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := Subgroup.zpowers α
  have hA : IsPGroup 2 A := by
    intro a
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    rw [Subgroup.coe_pow, pow_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hα, one_zpow, Subgroup.coe_one]
  have hodd : ¬ 2 ∣ Nat.card (Sylow 2 G) := by
    have h := card_sylow_modEq_one 2 G
    intro hdvd
    have h2 : Nat.card (Sylow 2 G) % 2 = 1 := h
    omega
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 G) hodd
  refine ⟨P, ?_⟩
  have h : α • P = P := hP ⟨α, Subgroup.mem_zpowers α⟩
  have h' := congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) h
  simp only [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h'
  have hhom : (α : G →* G) = MulDistribMulAction.toMonoidEnd (MulAut G) G α := by
    ext x
    rfl
  rw [hhom]
  exact h'

end Restrict

section Counting

variable {L : Type*} [Group L]

theorem fixed_quotient_mul_inv_mem (α : MulAut L) (hα : α ^ 2 = 1) (Z P : Subgroup L)
    (hZc : Z ≤ Subgroup.center L) (hZP : Z ≤ P) (hZα : Z.map (α : L →* L) = Z)
    (hZcyc : IsCyclic Z) (hfix : ∀ p ∈ P, α p = p → p ∈ Z) {t₁ t₂ : L} (ht₁ : t₁ ∈ P)
    (ht₂ : t₂ ∈ P) (hd₁ : t₁⁻¹ * α t₁ ∈ Z) (hd₂ : t₂⁻¹ * α t₂ ∈ Z) (hn₁ : t₁ ∉ Z)
    (hn₂ : t₂ ∉ Z) : t₁ * t₂⁻¹ ∈ Z := by
  have hcen : ∀ z ∈ Z, ∀ g : L, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp (hZc hz) g
  have hαZ : ∀ z ∈ Z, α z ∈ Z := fun z hz => hZα ▸ Subgroup.mem_map_of_mem _ hz
  have hαα : ∀ g : L, α (α g) = g := fun g => by
    rw [← MulAut.mul_apply, ← sq, hα]
    rfl
  let g : Z →* Z :=
    { toFun := fun w => ⟨(w : L)⁻¹ * α w, Z.mul_mem (Z.inv_mem w.2) (hαZ _ w.2)⟩
      map_one' := by ext; simp
      map_mul' := fun w₁ w₂ => by
        ext
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        have h := hcen _ (Z.mul_mem (Z.inv_mem w₁.2) (hαZ _ w₁.2)) (w₂ : L)⁻¹
        calc (w₂ : L)⁻¹ * (w₁ : L)⁻¹ * (α w₁ * α w₂)
            = ((w₂ : L)⁻¹ * ((w₁ : L)⁻¹ * α w₁)) * α w₂ := by group
          _ = (((w₁ : L)⁻¹ * α w₁) * (w₂ : L)⁻¹) * α w₂ := by rw [h]
          _ = (w₁ : L)⁻¹ * α w₁ * ((w₂ : L)⁻¹ * α w₂) := by group }
  let B : Subgroup Z := g.range
  have : IsCyclic (Z ⧸ B) := isCyclic_of_surjective _ (QuotientGroup.mk'_surjective B)
  have key2 : ∀ t ∈ P, ∀ (hd : t⁻¹ * α t ∈ Z), (⟨t⁻¹ * α t, hd⟩ : Z) ∈ B → t ∈ Z := by
    rintro t htP hd ⟨w, hw⟩
    have hw' : (w : L)⁻¹ * α w = t⁻¹ * α t := congrArg Subtype.val hw
    have hfixed : α (t * (w : L)⁻¹) = t * (w : L)⁻¹ := by
      have hαt : α t = t * ((w : L)⁻¹ * α w) := by rw [hw']; group
      rw [map_mul, map_inv, hαt]
      group
    have hmem := hfix _ (P.mul_mem htP (P.inv_mem (hZP w.2))) hfixed
    have := Z.mul_mem hmem w.2
    rwa [inv_mul_cancel_right] at this
  have key1 : ∀ t : L, ∀ (hd : t⁻¹ * α t ∈ Z), (⟨t⁻¹ * α t, hd⟩ : Z) ^ 2 ∈ B := by
    intro t hd
    refine ⟨⟨t⁻¹ * α t, hd⟩⁻¹, ?_⟩
    apply Subtype.ext
    change ((t⁻¹ * α t)⁻¹)⁻¹ * α ((t⁻¹ * α t)⁻¹) = (t⁻¹ * α t) ^ 2
    rw [map_inv, map_mul, map_inv, hαα, sq]
    group
  have key3 : t₁ * t₂⁻¹ = t₁ * t₂⁻¹ := rfl
  clear key3
  set d₁ : Z := ⟨t₁⁻¹ * α t₁, hd₁⟩ with hd₁def
  set d₂ : Z := ⟨t₂⁻¹ * α t₂, hd₂⟩ with hd₂def
  have hne₁ : (QuotientGroup.mk' B d₁ : Z ⧸ B) ≠ 1 := by
    intro h
    exact hn₁ (key2 t₁ ht₁ hd₁ ((QuotientGroup.eq_one_iff _).mp h))
  have hne₂ : (QuotientGroup.mk' B d₂ : Z ⧸ B) ≠ 1 := by
    intro h
    exact hn₂ (key2 t₂ ht₂ hd₂ ((QuotientGroup.eq_one_iff _).mp h))
  have hsq₁ : (QuotientGroup.mk' B d₁ : Z ⧸ B) ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (key1 t₁ hd₁)
  have hsq₂ : (QuotientGroup.mk' B d₂ : Z ⧸ B) ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (key1 t₂ hd₂)
  have heq := CFSG.RankTwoShapes.eq_of_sq_eq_one_of_isCyclic hsq₁ hne₁ hsq₂ hne₂
  have hB : d₁ * d₂⁻¹ ∈ B := by
    have h := QuotientGroup.eq.mp heq
    have hinv := B.inv_mem h
    rwa [mul_inv_rev, inv_inv, show d₂⁻¹ * d₁ = d₁ * d₂⁻¹ from
      Subtype.ext (hcen _ hd₁ ((d₂⁻¹ : Z) : L))] at hinv
  have hprod : (t₁ * t₂⁻¹)⁻¹ * α (t₁ * t₂⁻¹) = (t₁⁻¹ * α t₁) * (t₂⁻¹ * α t₂)⁻¹ := by
    have hc₁ := hcen _ hd₁ t₂
    have hc₂ : α t₂ * t₂⁻¹ = t₂⁻¹ * α t₂ := by
      have := hcen _ hd₂ t₂
      calc α t₂ * t₂⁻¹ = t₂ * (t₂⁻¹ * α t₂) * t₂⁻¹ := by group
        _ = (t₂⁻¹ * α t₂) * t₂ * t₂⁻¹ := by rw [this]
        _ = t₂⁻¹ * α t₂ := by group
    rw [map_mul, map_inv]
    calc (t₁ * t₂⁻¹)⁻¹ * (α t₁ * (α t₂)⁻¹)
        = t₂ * (t₁⁻¹ * α t₁) * (α t₂)⁻¹ := by group
      _ = (t₁⁻¹ * α t₁) * t₂ * (α t₂)⁻¹ := by rw [hc₁]
      _ = (t₁⁻¹ * α t₁) * (α t₂ * t₂⁻¹)⁻¹ := by group
      _ = (t₁⁻¹ * α t₁) * (t₂⁻¹ * α t₂)⁻¹ := by rw [hc₂]
  have hd : (t₁ * t₂⁻¹)⁻¹ * α (t₁ * t₂⁻¹) ∈ Z := by
    rw [hprod]
    exact Z.mul_mem hd₁ (Z.inv_mem hd₂)
  apply key2 _ (P.mul_mem ht₁ (P.inv_mem ht₂)) hd
  have : (⟨(t₁ * t₂⁻¹)⁻¹ * α (t₁ * t₂⁻¹), hd⟩ : Z) = d₁ * d₂⁻¹ := Subtype.ext hprod
  rw [this]
  exact hB

end Counting

section Quotient

variable {L : Type*} [Group L] [Finite L]

theorem card_le_two_of_forall_ne_one_eq {H : Type*} [Group H] [Finite H]
    (h : ∀ a b : H, a ≠ 1 → b ≠ 1 → a = b) : Nat.card H ≤ 2 := by
  by_cases htriv : ∃ a : H, a ≠ 1
  · obtain ⟨a, ha⟩ := htriv
    have hsub : (Set.univ : Set H) ⊆ {1, a} := by
      intro x _
      by_cases hx : x = 1
      · simp [hx]
      · simp [h x a hx ha]
    calc Nat.card H = Set.ncard (Set.univ : Set H) := (Set.ncard_univ H).symm
      _ ≤ Set.ncard ({1, a} : Set H) := Set.ncard_le_ncard hsub
      _ ≤ Set.ncard ({a} : Set H) + 1 := Set.ncard_insert_le 1 {a}
      _ = 2 := by rw [Set.ncard_singleton]
  · push Not at htriv
    have : Subsingleton H := ⟨fun a b => (htriv a).trans (htriv b).symm⟩
    rw [Nat.card_unique]
    omega

omit [Finite L] in
theorem map_mk_congr_eq (α : MulAut L) (Z : Subgroup L) [Z.Normal]
    (hZα : Z.map (α : L →* L) = Z) (P : Subgroup L) (hPα : P.map (α : L →* L) = P) :
    (P.map (QuotientGroup.mk' Z)).map
      ((QuotientGroup.congr Z Z α hZα : MulAut (L ⧸ Z)) : L ⧸ Z →* L ⧸ Z) =
      P.map (QuotientGroup.mk' Z) := by
  rw [Subgroup.map_map]
  have hcomp : ((QuotientGroup.congr Z Z α hZα : MulAut (L ⧸ Z)) : L ⧸ Z →* L ⧸ Z).comp
      (QuotientGroup.mk' Z) = (QuotientGroup.mk' Z).comp (α : L →* L) := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, hPα]

theorem card_fixedSubgroup_quotient_le_two (α : MulAut L) (hα : α ^ 2 = 1) (Z P : Subgroup L)
    [Z.Normal] (hZc : Z ≤ Subgroup.center L) (hZP : Z ≤ P) (hZα : Z.map (α : L →* L) = Z)
    (hZcyc : IsCyclic Z) (hfix : ∀ p ∈ P, α p = p → p ∈ Z)
    (hPα : (P.map (QuotientGroup.mk' Z)).map
      ((QuotientGroup.congr Z Z α hZα : MulAut (L ⧸ Z)) : L ⧸ Z →* L ⧸ Z) =
      P.map (QuotientGroup.mk' Z)) :
    Nat.card (fixedSubgroup (restrictAut (QuotientGroup.congr Z Z α hZα)
      (P.map (QuotientGroup.mk' Z)) hPα)) ≤ 2 := by
  apply card_le_two_of_forall_ne_one_eq
  have hlift : ∀ a : fixedSubgroup (restrictAut (QuotientGroup.congr Z Z α hZα)
      (P.map (QuotientGroup.mk' Z)) hPα), a ≠ 1 →
      ∃ t ∈ P, t⁻¹ * α t ∈ Z ∧ t ∉ Z ∧ (((a : _) : L ⧸ Z) = QuotientGroup.mk' Z t) := by
    rintro ⟨⟨q, hq⟩, hfixq⟩ ha
    obtain ⟨t, htP, rfl⟩ := hq
    have hfix' := congrArg Subtype.val ((mem_fixedSubgroup).mp hfixq)
    rw [restrictAut_apply] at hfix'
    change QuotientGroup.congr Z Z α hZα (QuotientGroup.mk t) = QuotientGroup.mk t at hfix'
    rw [QuotientGroup.congr_mk] at hfix'
    refine ⟨t, htP, ?_, ?_, rfl⟩
    · have := QuotientGroup.eq.mp hfix'.symm
      exact this
    · intro htZ
      apply ha
      apply Subtype.ext
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff t).mpr htZ
  intro a b ha hb
  obtain ⟨t₁, ht₁, hd₁, hn₁, he₁⟩ := hlift a ha
  obtain ⟨t₂, ht₂, hd₂, hn₂, he₂⟩ := hlift b hb
  have hmem := fixed_quotient_mul_inv_mem α hα Z P hZc hZP hZα hZcyc hfix ht₁ ht₂ hd₁ hd₂
    hn₁ hn₂
  apply Subtype.ext
  apply Subtype.ext
  rw [he₁, he₂]
  apply QuotientGroup.eq.mpr
  have h := (inferInstance : Z.Normal).conj_mem _ (Z.inv_mem hmem) t₁⁻¹
  rw [mul_inv_rev, inv_inv, inv_inv] at h
  have heq : t₁⁻¹ * (t₂ * t₁⁻¹) * t₁ = t₁⁻¹ * t₂ := by group
  rwa [heq] at h


theorem twoRank_eq_one_of_sylow (P : Sylow 2 L) (hP : AtMostOneInvolution (P : Subgroup L))
    (hne : (P : Subgroup L) ≠ ⊥) : twoRank L = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · apply csSup_le'
    rintro k ⟨E, -, hE, hcard⟩
    have hE2 : IsPGroup 2 E := fun e => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hE.2 e e.2)⟩
    obtain ⟨Q, hEQ⟩ := hE2.exists_le_sylow
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq L P Q
    have hconj : ∀ a ∈ E, g⁻¹ * a * g ∈ (P : Subgroup L) := by
      intro a ha
      have haQ : a ∈ MulAut.conj g • (P : Subgroup L) := hEQ ha
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at haQ
      have : (MulAut.conj g)⁻¹ • a = g⁻¹ * a * g := by
        rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
      rwa [this] at haQ
    have hcardE : Nat.card E ≤ 2 := by
      apply card_le_two_of_forall_ne_one_eq
      rintro ⟨a, ha⟩ ⟨b, hb⟩ ha1 hb1
      have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
      have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
      have hao : orderOf (g⁻¹ * a * g) = 2 := by
        rw [show g⁻¹ * a * g = MulAut.conj g⁻¹ a by simp, MulEquiv.orderOf_eq]
        exact orderOf_eq_prime (hE.2 a ha) ha1'
      have hbo : orderOf (g⁻¹ * b * g) = 2 := by
        rw [show g⁻¹ * b * g = MulAut.conj g⁻¹ b by simp, MulEquiv.orderOf_eq]
        exact orderOf_eq_prime (hE.2 b hb) hb1'
      have h := hP ⟨_, hconj a ha⟩ ⟨_, hconj b hb⟩
        (by rw [Subgroup.orderOf_mk]; exact hao) (by rw [Subgroup.orderOf_mk]; exact hbo)
      have h' : g⁻¹ * a * g = g⁻¹ * b * g := congrArg Subtype.val h
      apply Subtype.ext
      simpa using h'
    rw [hcard] at hcardE
    by_contra hk
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · obtain ⟨⟨p, hp⟩, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hp1' : p ≠ 1 := fun h => hp1 (Subtype.ext h)
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hp⟩
    have hk' : p ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : 2 ∣ orderOf p := by
      have h1 : orderOf p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      rcases j with _ | j
      · rw [pow_zero, orderOf_eq_one_iff] at hj
        exact absurd hj hp1'
      · rw [hj]
        exact dvd_pow_self 2 (Nat.succ_ne_zero j)
    set u := p ^ (orderOf p / 2) with hu
    have huo : orderOf u = 2 := orderOf_pow_orderOf_div (orderOf_pos p).ne' hdvd
    apply CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary L (Subgroup.zpowers u)
    · refine ⟨inferInstance, ?_⟩
      intro x hx
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        ← huo, pow_orderOf_eq_one, one_zpow]
    · rw [Nat.card_zpowers, huo, pow_one]

theorem sylow_not_le_center (hL : IsQuasisimple L) (P : Sylow 2 L) :
    ¬ (P : Subgroup L) ≤ Subgroup.center L := by
  intro hPZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect L := ⟨hL.1⟩
  have h8 := central_sylow_commutator P hPZ P.isPGroup'
  rw [show commutator L = ⊤ from hL.1, inf_top_eq] at h8
  have hab : commutator (P : Subgroup L) = ⊥ := by
    rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    apply Subgroup.mem_bot.mpr
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hPZ a.2) b).symm
  rw [hab, Subgroup.map_bot, inf_bot_eq] at h8
  have hodd : Odd (Nat.card L) := by
    have h := P.not_dvd_index
    rw [h8, Subgroup.index_bot] at h
    exact Nat.odd_iff.mpr (by omega)
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Nontrivial L := by
    have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2
    obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (L ⧸ Subgroup.center L))
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a', b', fun h => hab (congrArg _ h)⟩⟩
  exact Group.IsPerfect.not_isSolvable L hsolv

end Quotient

section Dihedral

variable {P : Type*} [Group P] [Finite P]

theorem exists_fixed_ne_one (hP : IsPGroup 2 P) [Nontrivial P] (β : MulAut P)
    (hβ : β ^ 2 = 1) : ∃ p : P, p ≠ 1 ∧ β p = p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := Subgroup.zpowers β
  have hA : IsPGroup 2 A := by
    intro a
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    rw [Subgroup.coe_pow, pow_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hβ, one_zpow, Subgroup.coe_one]
  have hmod := hA.card_modEq_card_fixedPoints P
  have heven : 2 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rcases n with _ | n
    · rw [pow_zero] at hn
      exact absurd (Nat.card_eq_one_iff_unique.mp hn).1 (not_subsingleton P)
    · rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  have hfix2 : 2 ∣ Nat.card (MulAction.fixedPoints A P) :=
    (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr heven)))
  have hone : (1 : P) ∈ MulAction.fixedPoints A P := fun a => smul_one a
  have hpos : 0 < Nat.card (MulAction.fixedPoints A P) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, hone⟩⟩, inferInstance⟩
  have hlt : 1 < (MulAction.fixedPoints A P).ncard := by
    rw [← Nat.card_coe_set_eq]
    obtain ⟨k, hk⟩ := hfix2
    omega
  obtain ⟨p, hp, hp1⟩ := Set.exists_ne_of_one_lt_ncard hlt 1
  exact ⟨p, hp1, hp ⟨β, Subgroup.mem_zpowers β⟩⟩


end Dihedral

end CFSG.ComponentClassification.AschbacherToolkit
