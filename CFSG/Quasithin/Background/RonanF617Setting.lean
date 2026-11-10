module

public import CFSG.LocalAnalysis.SectionRank.QTK.ExcRee
public import CFSG.Quasithin.Background.F6NQStructure

public section

namespace CFSG.Quasithin.RonanF617

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F6
open CFSG.Quasithin.F6.F617Setting (exists_ne_one_commute exists_inv_mod_pCoreOf)

structure Setting {D : Type} [Group D] [Finite D] (G₁ G₂ K : Subgroup D) : Prop where
  triple : IsGoldschmidtTriple G₁ G₂
  pPrimeCore_eq_bot : CFSG.pPrimeCore 3 D = ⊥
  pCore_eq_bot : Open.pCore 2 D = ⊥
  component : CFSG.IsComponent K
  normal : K.Normal
  le_left : twoResidual G₁ ≤ K
  not_le_right : ¬ twoResidual G₂ ≤ K
  card_left : Nat.card ↥(twoResidual G₁) = 3

namespace Setting

variable {D : Type} [Group D] [Finite D] {G₁ G₂ K : Subgroup D}

theorem sup_eq_top (hS : Setting G₁ G₂ K) : K ⊔ G₂ = ⊤ :=
  sup_eq_top_of_twoResidual_le hS.triple hS.le_left

theorem inf_eq (hS : Setting G₁ G₂ K) :
    G₂ ⊓ K = pCoreOf 2 G₂ ⊓ K ∧ pCoreOf 2 G₂ ⊓ K = G₂ ⊓ G₁ ⊓ K ∧
      IsSylowTwoOf (G₂ ⊓ G₁ ⊓ K) K := by
  have := hS.normal
  exact ((tfae_inf_le_pCoreOf hS.triple.symm isSubnormal_top_of_normal).out 3 2).mp
    hS.not_le_right

theorem isSylowTwoOf_inf (hS : Setting G₁ G₂ K) : IsSylowTwoOf (pCoreOf 2 G₂ ⊓ K) K := by
  obtain ⟨-, e2, hsyl⟩ := hS.inf_eq
  rw [e2]
  exact hsyl

theorem elemAbelian (hS : Setting G₁ G₂ K) :
    IsElemAbelian 2 (pCoreOf 2 G₂) ∧ Nat.card ↥(pCoreOf 2 G₂) ≤ 2 ^ 3 :=
  (f6_13_three hS.triple hS.pCore_eq_bot hS.card_left).1

theorem isPGroup_center (hS : Setting G₁ G₂ K) :
    IsPGroup 3 ↥(Subgroup.center ↥K) :=
  have := hS.normal
  isPGroup_center_of_pPrimeCore_eq_bot hS.pPrimeCore_eq_bot

theorem odd_card_center (hS : Setting G₁ G₂ K) :
    Odd (Nat.card ↥(Subgroup.center ↥K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hS.isPGroup_center.exists_card_eq
  rw [hk]
  exact Odd.pow (by decide)

theorem normal_inf_centralizer (hS : Setting G₁ G₂ K) :
    (K ⊓ Subgroup.centralizer (K : Set D)).Normal := by
  have hKn := hS.normal
  refine ⟨fun z hz g => Subgroup.mem_inf.mpr ⟨hKn.conj_mem z hz.1 g, ?_⟩⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : g⁻¹ * k * g ∈ K := by simpa using hKn.conj_mem k hk g⁻¹
  have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hk'
  calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * k := by group

theorem not_le_inf_centralizer (hS : Setting G₁ G₂ K) :
    ¬ twoResidual G₁ ≤ K ⊓ Subgroup.centralizer (K : Set D) := by
  intro hle
  set Z := K ⊓ Subgroup.centralizer (K : Set D) with hZ
  have := hS.normal_inf_centralizer
  have hsup : Z ⊔ G₂ = ⊤ := sup_eq_top_of_twoResidual_le hS.triple hle
  have hZab : Group.IsSolvable ↥Z := Group.isSolvable_of_comm fun a b => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1)
  have : Group.IsSolvable ↥G₂ := isSolvable_vertex_right hS.triple
  have hsurj : Function.Surjective ((QuotientGroup.mk' Z).comp G₂.subtype) := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective Z q
    have hd : d ∈ Z ⊔ G₂ := hsup ▸ Subgroup.mem_top d
    rw [Subgroup.mem_sup_of_normal_left] at hd
    obtain ⟨z, hz, g, hg, rfl⟩ := hd
    refine ⟨⟨g, hg⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have h1 := hS.normal_inf_centralizer.conj_mem z hz g⁻¹
    rw [inv_inv, mul_assoc] at h1
    exact h1
  have : Group.IsSolvable (D ⧸ Z) := Group.isSolvable_of_surjective hsurj
  have : Group.IsSolvable D := Group.isSolvable_of_subgroup_quotient Z
  have : Group.IsPerfect ↥K := hS.component.1.1
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hS.component.1
  exact Group.IsPerfect.not_isSolvable ↥K inferInstance


theorem exists_sylow_eq (hS : Setting G₁ G₂ K) :
    ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K) = (pCoreOf 2 G₂ ⊓ K).subgroupOf K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := hS.isSylowTwoOf_inf
  exact ⟨(hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm).toSylow hsyl.2.2, rfl⟩

theorem four_le_card_inf (hS : Setting G₁ G₂ K) : 4 ≤ Nat.card ↥(pCoreOf 2 G₂ ⊓ K) := by
  have hq : CFSG.IsQuasisimple ↥K := hS.component.1
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2.1
  obtain ⟨P, hP⟩ := hS.exists_sylow_eq
  obtain ⟨Q, ⟨eQ⟩⟩ := exists_sylow_quotient_mulEquiv _ hS.odd_card_center P
  have h4 := (not_isCyclic_sylow_two hq.2.2 Q).2
  have hPQ : Nat.card ↥(P : Subgroup ↥K) = Nat.card ↥(pCoreOf 2 G₂ ⊓ K) := by
    rw [hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← hPQ, Nat.card_congr eQ.toEquiv]
  exact Nat.le_of_dvd Nat.card_pos h4

theorem exists_generator (hS : Setting G₁ G₂ K) :
    ∃ x ∈ twoResidual G₁, orderOf x = 3 ∧ x ∉ Subgroup.centralizer (K : Set D) ∧
      ∀ q ∈ pCoreOf 2 G₂, q * x * q⁻¹ = x ∨ q * x * q⁻¹ = x⁻¹ := by
  have h := hS.triple
  set L₁ := twoResidual G₁ with hL₁
  obtain ⟨x, hxL, hx1⟩ : ∃ x ∈ L₁, x ≠ 1 := by
    by_contra hne
    push Not at hne
    have : L₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hne
    have h3 := hS.card_left
    rw [← hL₁, this, Subgroup.card_bot] at h3
    omega
  have hord : orderOf x = 3 := by
    have h1 : orderOf x ∣ 3 := hS.card_left ▸ Subgroup.orderOf_dvd_natCard L₁ hxL
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hx1
    · exact h2
  refine ⟨x, hxL, hord, fun hxC => ?_, fun q hq => ?_⟩
  ·
    apply hS.not_le_inf_centralizer
    intro y hy
    refine ⟨hS.le_left hy, ?_⟩
    rcases mem_of_card_eq_three hS.card_left hxL hx1 hy with rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hxC
    · exact Subgroup.inv_mem _ hxC
  · have hqT : q ∈ G₁ ⊓ G₂ := pCoreOf_le_inf_right h hq
    have hqN := le_normalizer_twoResidual G₁ (Subgroup.mem_inf.mp hqT).1
    have hmem := (Subgroup.mem_normalizer_iff.mp hqN x).mp hxL
    rcases mem_of_card_eq_three hS.card_left hxL hx1 hmem with h1 | h1 | h1
    · exfalso
      apply hx1
      calc x = q⁻¹ * (q * x * q⁻¹) * q := by group
        _ = 1 := by rw [h1]; group
    · exact Or.inl h1
    · exact Or.inr h1


theorem pCoreOf_inf_centralizer (hS : Setting G₁ G₂ K) :
    pCoreOf 2 G₂ ⊓ Subgroup.centralizer (K : Set D) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hS.triple
  have hCn := normal_centralizer_of_normal hS.normal
  set M := pCoreOf 2 G₂ ⊓ Subgroup.centralizer (K : Set D) with hM
  have hG₂ : G₂ ≤ Subgroup.normalizer (M : Set D) := fun g hg =>
    mem_normalizer_of_forall_conj_mem fun m hm =>
      ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂ hg) m).mp hm.1,
        hCn.conj_mem m hm.2 g⟩
  have hL₁ : twoResidual G₁ ≤ Subgroup.normalizer (M : Set D) := fun l hl =>
    mem_normalizer_of_forall_conj_mem fun m hm => by
      have hc := Subgroup.mem_centralizer_iff.mp hm.2 l (hS.le_left hl)
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact hm
  have hMn : M.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff, ← h.gen]
    refine sup_le ?_ hG₂
    rw [← inf_sup_twoResidual_left h]
    exact sup_le (inf_le_right.trans hG₂) hL₁
  have hM2 : IsPGroup 2 M := (pCoreOf_isPGroup 2 G₂).to_le inf_le_left
  have hle := le_pCore 2 hMn hM2
  rw [hS.pCore_eq_bot] at hle
  exact le_bot_iff.mp hle

theorem inf_centralizer_eq_bot (hS : Setting G₁ G₂ K) :
    G₂ ⊓ Subgroup.centralizer (K : Set D) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hS.triple
  have hCn := normal_centralizer_of_normal hS.normal
  set N := G₂ ⊓ Subgroup.centralizer (K : Set D) with hN
  set Q₂ := pCoreOf 2 G₂ with hQ₂
  set L₁ := twoResidual G₁ with hL₁
  by_contra hne
  have hNQ : ¬ N ≤ Q₂ := by
    intro hle
    apply hne
    rw [eq_bot_iff, ← hS.pCoreOf_inf_centralizer]
    exact le_inf hle inf_le_right
  have hNsub : IsSubnormal N G₂ := by
    refine IsSubnormal.step inf_le_left ⟨fun n hn g => ?_⟩ (IsSubnormal.refl G₂)
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨G₂.mul_mem (G₂.mul_mem g.2 hn.1) (G₂.inv_mem g.2), hCn.conj_mem _ hn.2 g⟩
  have hL₂N : twoResidual G₂ ≤ N := twoResidual_le_of_isSubnormal h.symm hNsub hNQ
  obtain ⟨D₂, hD₂, -⟩ := exists_isSylowIn_ge 3 (H := G₂) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  have hD₂C : D₂ ≤ Subgroup.centralizer (K : Set D) := by
    intro d hd
    refine (hL₂N (mem_twoResidual_of_odd (hD₂.1 hd) ?_)).2
    obtain ⟨k, hk⟩ := hD₂.2.1 ⟨d, hd⟩
    have h1 : orderOf d ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    exact Odd.of_dvd_nat (Odd.pow (by decide)) h1
  obtain ⟨x, hxL, hxo, -, hxn⟩ := hS.exists_generator
  have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hxo; norm_num at hxo
  obtain ⟨e, heQK, he1, hex⟩ := exists_ne_one_commute (P := Q₂ ⊓ K)
    (IsElemAbelian.mono hS.elemAbelian.1 inf_le_left) hS.four_le_card_inf fun q hq => hxn q hq.1
  set S := Q₂ ⊓ K ⊓ Subgroup.centralizer (L₁ : Set D) with hSdef
  have heS : e ∈ S := by
    refine ⟨heQK, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rcases mem_of_card_eq_three hS.card_left hxL hx1 hy with rfl | rfl | rfl
    · simp
    · exact hex.symm
    · calc x⁻¹ * e = x⁻¹ * (e * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * e) * x⁻¹ := by rw [hex]
        _ = e * x⁻¹ := by group
  have hSD : D₂ ≤ Subgroup.normalizer (S : Set D) := fun d hd =>
    mem_normalizer_of_forall_conj_mem fun s hs => by
      have hc := Subgroup.mem_centralizer_iff.mp (hD₂C hd) s hs.1.2
      rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
      exact hs
  have hSn : Q₂ ⊔ L₁ ≤ Subgroup.normalizer (S : Set D) := by
    refine sup_le (fun q hq => mem_normalizer_of_forall_conj_mem fun s hs => ?_)
      (fun l hl => mem_normalizer_of_forall_conj_mem fun s hs => ?_)
    · refine ⟨⟨Q₂.mul_mem (Q₂.mul_mem hq hs.1.1) (Q₂.inv_mem hq),
        hS.normal.conj_mem s hs.1.2 q⟩, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      have hqT : q ∈ G₁ ⊓ G₂ := pCoreOf_le_inf_right h hq
      have hqN := le_normalizer_twoResidual G₁ (G₁.inv_mem (Subgroup.mem_inf.mp hqT).1)
      have hl' : q⁻¹ * l * q⁻¹⁻¹ ∈ L₁ := (Subgroup.mem_normalizer_iff.mp hqN l).mp hl
      rw [inv_inv] at hl'
      have hc := Subgroup.mem_centralizer_iff.mp hs.2 _ hl'
      calc l * (q * s * q⁻¹) = q * ((q⁻¹ * l * q) * s) * q⁻¹ := by group
        _ = q * (s * (q⁻¹ * l * q)) * q⁻¹ := by rw [hc]
        _ = q * s * q⁻¹ * l := by group
    · have hc := Subgroup.mem_centralizer_iff.mp hs.2 l hl
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact hs
  have hS0 := eq_bot_of_le_pCoreOf_of_normalizes h hS.pCore_eq_bot hD₂
    (inf_le_left.trans inf_le_left) hSD hSn
  have he0 : e ∈ (⊥ : Subgroup D) := by
    rw [← hS0]
    exact heS
  exact he1 (Subgroup.mem_bot.mp he0)


theorem odd_card_centralizer (hS : Setting G₁ G₂ K) :
    Odd (Nat.card (Subgroup.centralizer (K : Set D))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hS.triple
  have hCn := normal_centralizer_of_normal hS.normal
  set C := Subgroup.centralizer (K : Set D) with hC
  have hsyl := isSylowIn_inf_of_isSubnormal (X := C) isSubnormal_top_of_normal
    (isSylowTwoOf_inf_top h)
  have hTC : G₁ ⊓ G₂ ⊓ C = ⊥ := by
    rw [eq_bot_iff, ← hS.inf_centralizer_eq_bot]
    exact inf_le_inf_right C inf_le_right
  have h2 := hsyl.2.2
  rw [hTC, Subgroup.relIndex, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h2
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)

theorem centralizer_le_twoResidual (hS : Setting G₁ G₂ K) :
    Subgroup.centralizer (K : Set D) ≤ twoResidual ⊤ := fun c hc =>
  mem_twoResidual_of_odd (Subgroup.mem_top c)
    (Odd.of_dvd_nat hS.odd_card_centralizer (Subgroup.orderOf_dvd_natCard _ hc))


end Setting

end CFSG.Quasithin.RonanF617
