module

public import CFSG.Walter.W67.Statements
public import CFSG.Walter.W67.Section4.Cor44A
import CFSG.Walter.W67.Section4.Lemma42
import CFSG.Walter.W67.Section4.Prop43cA
import CFSG.Walter.W67.Section4.Prop43ab
import CFSG.Walter.W67.Section4.Basic
import CFSG.Walter.W67.W2Cor32A

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_commutator' [Finite G] {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have hmap : ∀ X : Subgroup G, g ∈ Subgroup.normalizer (X : Set G) →
      X.map (MulAut.conj g).toMonoidHom = X := by
    intro X hX
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
    · obtain ⟨y, hy, rfl⟩ := hx
      exact (Subgroup.mem_normalizer_iff.mp hX y).mp hy
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have h1 : ⁅H, K⁆.map (MulAut.conj g).toMonoidHom = ⁅H, K⁆ := by
    rw [Subgroup.map_commutator, hmap H hH, hmap K hK]
  refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
  rw [← h1]
  exact ⟨x, hx, rfl⟩

theorem eq_of_card_eq_of_le_cyclic {A B C : Subgroup G} (hA : IsCyclic A) (hBA : B ≤ A)
    (hCA : C ≤ A) (hcard : Nat.card B = Nat.card C) : B = C := by
  have hc : Nat.card (B.subgroupOf A) = Nat.card (C.subgroupOf A) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv, hcard]
  have heq : B.subgroupOf A = C.subgroupOf A := (IsCyclic.subgroup_eq_iff_card_eq).mpr hc
  have h1 := congrArg (Subgroup.map A.subtype) heq
  rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hBA, inf_eq_left.mpr hCA] at h1

namespace Std

variable (s : Std G) {T₂ : G}

theorem A_comm
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) :
    ∀ x ∈ s.fr.A T₂, ∀ y ∈ s.fr.A T₂, x * y = y * x := by
  have hcycA := s.isCyclic_A hp hT₂ h2
  intro x hx y hy
  exact congrArg Subtype.val
    ((IsCyclic.isMulCommutative (α := s.fr.A T₂)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem E_le_normalizer_A (hT₂ : T₂ ∈ s.fr.T) :
    s.fr.E ≤ Subgroup.normalizer (s.fr.A T₂ : Set G) := fun _ he =>
  JT.mem_normalizer_of_conj_mem fun _ hx => s.fr.E_conj_mem_A he hx hT₂

theorem A_decomp
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    (hcop : Nat.Coprime (Nat.card (s.fr.A T₂)) (Nat.card s.fr.E)) :
    s.fr.A₀ T₂ ⊔ s.fr.A₁ T₂ = s.fr.A T₂ ∧ s.fr.A₀ T₂ ⊓ s.fr.A₁ T₂ = ⊥ ∧
      Nat.Coprime (Nat.card (s.fr.A₀ T₂)) (Nat.card (s.fr.A₁ T₂)) ∧
      s.fr.A₁ T₂ ≤ s.fr.A T₂ ∧ s.fr.E ≤ Subgroup.normalizer (s.fr.A₁ T₂ : Set G) := by
  have hcycA := s.isCyclic_A hp hT₂ h2
  have hab := s.A_comm hp hT₂ h2
  obtain ⟨g₀, hg₀⟩ := s.exists_E_eq_zpowers
  have hg₀E : g₀ ∈ s.fr.E := hg₀ ▸ Subgroup.mem_zpowers g₀
  obtain ⟨hdisj, hcard, hA₁A, hEA₁⟩ :=
    coprime_decomp hab hg₀ (s.E_le_normalizer_A hT₂ hg₀E) hcop
  change s.fr.A₀ T₂ ⊓ s.fr.A₁ T₂ = ⊥ at hdisj
  change Nat.card (s.fr.A₀ T₂) * Nat.card (s.fr.A₁ T₂) = Nat.card (s.fr.A T₂) at hcard
  change s.fr.A₁ T₂ ≤ s.fr.A T₂ at hA₁A
  change ∀ b ∈ s.fr.A₁ T₂, g₀ * b * g₀⁻¹ ∈ s.fr.A₁ T₂ at hEA₁
  have hA₀A : s.fr.A₀ T₂ ≤ s.fr.A T₂ := inf_le_left
  have hEN₁ : s.fr.E ≤ Subgroup.normalizer (s.fr.A₁ T₂ : Set G) := by
    rw [hg₀, Subgroup.zpowers_le]
    exact JT.mem_normalizer_of_conj_mem hEA₁
  obtain ⟨hcA, -⟩ := card_sup_mul_card_inf_of_commute (s.fr.A₀ T₂) (s.fr.A₁ T₂)
    (fun x hx y hy => hab x (hA₀A hx) y (hA₁A hy))
  rw [hdisj, Subgroup.card_bot, mul_one, hcard] at hcA
  have hA01 : s.fr.A₀ T₂ ⊔ s.fr.A₁ T₂ = s.fr.A T₂ :=
    Subgroup.eq_of_le_of_card_ge (sup_le hA₀A hA₁A) (by rw [hcA])
  refine ⟨hA01, hdisj, ?_, hA₁A, hEN₁⟩
  apply Nat.coprime_of_dvd
  intro r hr h0 h1
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := s.fr.A₀ T₂) r h0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := s.fr.A₁ T₂) r h1
  have hzx : Nat.card (Subgroup.zpowers (x : G)) = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hzy : Nat.card (Subgroup.zpowers (y : G)) = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy]
  have heq := eq_of_card_eq_of_le_cyclic hcycA (Subgroup.zpowers_le.mpr (hA₀A x.2))
    (Subgroup.zpowers_le.mpr (hA₁A y.2)) (by rw [hzx, hzy])
  have hxA₁ : (x : G) ∈ s.fr.A₁ T₂ := by
    have : (x : G) ∈ Subgroup.zpowers (y : G) := heq ▸ Subgroup.mem_zpowers _
    exact (Subgroup.zpowers_le.mpr y.2) this
  have h1' : (x : G) ∈ s.fr.A₀ T₂ ⊓ s.fr.A₁ T₂ := ⟨x.2, hxA₁⟩
  rw [hdisj, Subgroup.mem_bot] at h1'
  have : x = 1 := Subtype.ext h1'
  rw [this, orderOf_one] at hx
  exact hr.one_lt.ne' hx.symm

theorem E_le_normalizer_V (hT₂ : T₂ ∈ s.fr.T) :
    s.fr.E ≤ Subgroup.normalizer (s.fr.V T₂ : Set G) := fun e he =>
  JT.mem_normalizer_of_conj_mem fun v hv => by
    rw [(Subgroup.mem_centralizer_iff.mp (s.fr.E_le_CS he) v (s.fr.V_le_S hT₂ hv)).symm,
      mul_inv_cancel_right]
    exact hv


theorem A₀_comm
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) {a x : G}
    (ha : a ∈ s.fr.A₀ T₂) (hx : x ∈ s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E) : a * x = x * a := by
  have hab := s.A_comm hp hT₂ h2
  have hA₀A : s.fr.A₀ T₂ ≤ s.fr.A T₂ := inf_le_left
  have hC : s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E ≤ Subgroup.centralizer (s.fr.A₀ T₂ : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.le_centralizer_iff.mpr (hA₀A.trans (s.A_le_centralizer_V T₂))
    · exact fun y hy => Subgroup.mem_centralizer_iff.mpr fun z hz => hab z (hA₀A hz) y hy
    · exact Subgroup.le_centralizer_iff.mpr inf_le_right
  exact Subgroup.mem_centralizer_iff.mp (hC hx) a ha

theorem exists_decomp_X
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    (hcop : Nat.Coprime (Nat.card (s.fr.A T₂)) (Nat.card s.fr.E)) {x : G}
    (hx : x ∈ s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E) :
    ∃ a ∈ s.fr.A₀ T₂, ∃ y ∈ s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E, x = a * y := by
  obtain ⟨hA01, -, -, hA₁A, -⟩ := s.A_decomp hp hT₂ h2 hcop
  have hab := s.A_comm hp hT₂ h2
  have hA₀A : s.fr.A₀ T₂ ≤ s.fr.A T₂ := inf_le_left
  have hAV : s.fr.A T₂ ≤ Subgroup.normalizer (s.fr.V T₂ : Set G) :=
    (s.A_le_centralizer_V T₂).trans (Subgroup.centralizer_le_normalizer _)
  have hEVA : s.fr.E ≤ Subgroup.normalizer ((s.fr.V T₂ ⊔ s.fr.A T₂ : Subgroup G) : Set G) :=
    fun e he => mem_normalizer_sup (s.E_le_normalizer_V hT₂ he) (s.E_le_normalizer_A hT₂ he)
  obtain ⟨w, hw, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEVA).mp hx
  obtain ⟨v, hv, a, ha, rfl⟩ := (mem_sup_iff_of_le_normalizer hAV).mp hw
  have hA₁A₀ : s.fr.A₁ T₂ ≤ Subgroup.normalizer (s.fr.A₀ T₂ : Set G) := fun y hy =>
    JT.mem_normalizer_of_conj_mem fun z hz => by
      rw [hab y (hA₁A hy) z (hA₀A hz), mul_inv_cancel_right]
      exact hz
  have haA : a ∈ s.fr.A₀ T₂ ⊔ s.fr.A₁ T₂ := hA01 ▸ ha
  obtain ⟨a₀, ha₀, a₁, ha₁, rfl⟩ := (mem_sup_iff_of_le_normalizer hA₁A₀).mp haA
  refine ⟨a₀, ha₀, v * a₁ * e, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left
      (Subgroup.mem_sup_left hv)) (Subgroup.mem_sup_left (Subgroup.mem_sup_right ha₁)))
      (Subgroup.mem_sup_right he)
  · have hva : v * a₀ = a₀ * v := (s.A₀_comm hp hT₂ h2 ha₀
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hv))).symm
    calc v * (a₀ * a₁) * e = (v * a₀) * a₁ * e := by group
      _ = (a₀ * v) * a₁ * e := by rw [hva]
      _ = a₀ * (v * a₁ * e) := by group


end Std


end CFSG.Walter.W67
