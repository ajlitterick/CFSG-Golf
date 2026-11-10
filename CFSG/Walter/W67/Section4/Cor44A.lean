module

import CFSG.Walter.W67.Section4.Lemma42
import CFSG.Walter.W67.Section4.Lemma42B
import CFSG.Walter.W67.Section4.Prop43cA
import CFSG.Walter.W67.Section4.Prop43ab
import CFSG.Walter.W67.Section4.Basic
import CFSG.Walter.W67.W2Cor32A
public import CFSG.Walter.ReeOrder.JT.Section2
public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def S_prop_4_1_three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), RFacts → s.p = 3 → ∀ {r : ℕ}, r ∈ s.fr.σ →
    r = 3 ∨ r ∣ s.q ^ 2 - s.q + 1

theorem coprime_decomp {A E : Subgroup G} (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {e : G}
    (hE : E = Subgroup.zpowers e) (heA : e ∈ Subgroup.normalizer (A : Set G))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card E)) :
    (A ⊓ Subgroup.centralizer (E : Set G)) ⊓ ⁅E, A⁆ = ⊥ ∧
      Nat.card (A ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) *
        Nat.card (⁅E, A⁆ : Subgroup G) = Nat.card A ∧ ⁅E, A⁆ ≤ A ∧
      ∀ b ∈ ⁅E, A⁆, e * b * e⁻¹ ∈ ⁅E, A⁆ := by
  have hconj : ∀ x ∈ A, e * x * e⁻¹ ∈ A := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp heA x).mp hx
  let δ : A →* A :=
    { toFun := fun x => ⟨e * x * e⁻¹ * x⁻¹, A.mul_mem (hconj x x.2) (A.inv_mem x.2)⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        change e * ((x : G) * y) * e⁻¹ * ((x : G) * y)⁻¹ =
          (e * x * e⁻¹ * (x : G)⁻¹) * (e * y * e⁻¹ * (y : G)⁻¹)
        have hc := hab _ (A.inv_mem x.2) _ (A.mul_mem (hconj y y.2) (A.inv_mem y.2))
        calc e * ((x : G) * y) * e⁻¹ * ((x : G) * y)⁻¹
            = (e * x * e⁻¹) * ((e * y * e⁻¹ * (y : G)⁻¹) * (x : G)⁻¹) := by group
          _ = (e * x * e⁻¹) * ((x : G)⁻¹ * (e * y * e⁻¹ * (y : G)⁻¹)) := by rw [← hc]
          _ = (e * x * e⁻¹ * (x : G)⁻¹) * (e * y * e⁻¹ * (y : G)⁻¹) := by group }
  have hδ : ∀ x : A, (δ x : G) = e * x * e⁻¹ * (x : G)⁻¹ := fun x => rfl
  set B : Subgroup G := δ.range.map A.subtype with hB
  have hEmem : ∀ e' ∈ E, ∃ n : ℕ, e ^ n = e' := by
    intro e' he'
    rw [hE] at he'
    have : e' ∈ (Submonoid.powers e : Set G) := by rw [powers_eq_zpowers]; exact he'
    exact Submonoid.mem_powers_iff _ _ |>.mp this
  have hBA : B ≤ A := Subgroup.map_subtype_le _
  have hBmem : ∀ x : A, (δ x : G) ∈ B := fun x => ⟨δ x, ⟨x, rfl⟩, rfl⟩
  have hconjB : ∀ b ∈ B, e * b * e⁻¹ ∈ B := by
    intro b hb
    have hbA := hBA hb
    have : e * b * e⁻¹ = (e * b * e⁻¹ * b⁻¹) * b := by group
    rw [this]
    exact B.mul_mem (hBmem ⟨b, hbA⟩) hb
  have hpow : ∀ n : ℕ, ∀ a ∈ A, e ^ n * a * (e ^ n)⁻¹ * a⁻¹ ∈ B := by
    intro n
    induction n with
    | zero => intro a _; simp
    | succ n ih =>
      intro a ha
      have h1 := ih a ha
      set b := e ^ n * a * (e ^ n)⁻¹ * a⁻¹ with hb
      have hbA := hBA h1
      have h2 : e ^ (n + 1) * a * (e ^ (n + 1))⁻¹ * a⁻¹ =
          (e * b * e⁻¹) * (e * a * e⁻¹ * a⁻¹) := by
        rw [hb, pow_succ']
        group
      rw [h2]
      exact B.mul_mem (hconjB b h1) (hBmem ⟨a, ha⟩)
  have hEAB : ⁅E, A⁆ ≤ B := by
    rw [Subgroup.commutator_le]
    intro e' he' a ha
    obtain ⟨n, rfl⟩ := hEmem e' he'
    rw [commutatorElement_def]
    exact hpow n a ha
  have hBEA : B ≤ ⁅E, A⁆ := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have heE : e ∈ E := by rw [hE]; exact Subgroup.mem_zpowers e
    have := Subgroup.commutator_mem_commutator heE x.2
    rw [commutatorElement_def] at this
    exact this
  have hBeq : ⁅E, A⁆ = B := le_antisymm hEAB hBEA
  have hCE : ∀ x : G, x ∈ Subgroup.centralizer (E : Set G) ↔ x * e = e * x := by
    intro x
    rw [hE, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
  have hker : δ.ker.map A.subtype = A ⊓ Subgroup.centralizer (E : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, (hCE y).mpr ?_⟩
      have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      rw [hδ] at h1
      have h2 : e * (y : G) * e⁻¹ = y := by
        calc e * (y : G) * e⁻¹ = (e * y * e⁻¹ * (y : G)⁻¹) * y := by group
          _ = y := by rw [h1]; simp
      calc (y : G) * e = (e * y * e⁻¹) * e := by rw [h2]
        _ = e * y := by group
    · rintro ⟨hxA, hxC⟩
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      show δ ⟨x, hxA⟩ = 1
      ext
      rw [hδ]
      have h1 := (hCE x).mp hxC
      simp only [OneMemClass.coe_one]
      calc e * x * e⁻¹ * x⁻¹ = (x * e) * e⁻¹ * x⁻¹ := by rw [h1]
        _ = 1 := by group
  have hcard : Nat.card (A ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) *
      Nat.card (⁅E, A⁆ : Subgroup G) = Nat.card A := by
    rw [← hker, hBeq, Subgroup.card_map_of_injective A.subtype_injective,
      Subgroup.card_map_of_injective A.subtype_injective]
    exact Subgroup.card_ker_mul_card_range δ
  refine ⟨?_, hcard, hBeq ▸ hBA, fun b hb => hBeq ▸ hconjB b (hBeq ▸ hb)⟩
  rw [eq_bot_iff]
  rintro z ⟨⟨hzA, hzC⟩, hzB⟩
  rw [hBeq] at hzB
  obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hzB
  set z := (δ x : G) with hz
  have hze : z * e = e * z := (hCE z).mp hzC
  have hiter : ∀ n : ℕ, e ^ n * x * (e ^ n)⁻¹ = z ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hzc : Commute e (z ^ n) := (Commute.pow_right (Commute.symm hze) n).symm.symm
      have h1 : e * (x : G) * e⁻¹ = z * x := by rw [hz, hδ]; group
      calc e ^ (n + 1) * x * (e ^ (n + 1))⁻¹ = e * (e ^ n * x * (e ^ n)⁻¹) * e⁻¹ := by
            rw [pow_succ']; group
        _ = e * (z ^ n * x) * e⁻¹ := by rw [ih]
        _ = (e * z ^ n * e⁻¹) * (e * x * e⁻¹) := by group
        _ = z ^ n * (z * x) := by rw [h1, hzc.eq, mul_inv_cancel_right]
        _ = z ^ (n + 1) * x := by rw [pow_succ]; group
  have h1 := hiter (orderOf e)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have hzo : z ^ orderOf e = 1 := by
    have := congrArg (· * (x : G)⁻¹) h1
    simpa using this.symm
  have hoE : orderOf e = Nat.card E := by rw [hE, Nat.card_zpowers]
  have hd1 : orderOf z ∣ Nat.card E := hoE ▸ orderOf_dvd_of_pow_eq_one hzo
  have hd2 : orderOf z ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hzA
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd2 hd1)

omit [Finite G] in
theorem sup_aux4 {T A E : Subgroup G} : T ⊔ A ⊔ E = (A ⊔ E) ⊔ T :=
  le_antisymm (sup_le (sup_le le_sup_right (le_sup_of_le_left le_sup_left))
      (le_sup_of_le_left le_sup_right))
    (sup_le (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
      (le_sup_of_le_left le_sup_left))

namespace Std

variable (s : Std G) {T₂ : G}


theorem card_normalizer_V_dvd
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) :
    Nat.card (Subgroup.normalizer (s.fr.V T₂ : Set G)) ∣
      24 * (Nat.card (s.fr.A T₂) * Nat.card s.fr.E) := by
  obtain ⟨U, hU3, hNV, -, -, hT₁2, hC, -, hS⟩ := prop_4_3_ab G s.toHyp s.fr hp s.hidx hT₂ h2
  generalize hT₁ : (s.fr.S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) = T₁ at hT₁2 hC hS
  have hT₁S : T₁ ≤ (s.fr.S : Subgroup G) := hT₁ ▸ inf_le_left
  have hEA : s.fr.E ≤ Subgroup.normalizer (s.fr.A T₂ : Set G) := fun e he =>
    JT.mem_normalizer_of_conj_mem fun x hx => s.fr.E_conj_mem_A he hx hT₂
  have h1 : Nat.card (s.fr.A T₂ ⊔ s.fr.E : Subgroup G) ∣
      Nat.card (s.fr.A T₂) * Nat.card s.fr.E :=
    Dvd.intro _ (card_sup_mul_card_inf_of_le_normalizer hEA)
  have hT₁N : T₁ ≤ Subgroup.normalizer ((s.fr.A T₂ ⊔ s.fr.E : Subgroup G) : Set G) := by
    intro t ht
    refine mem_normalizer_sup (JT.mem_normalizer_of_conj_mem fun x hx =>
      s.fr.S_conj_mem_A (hT₁S ht) hx hT₂) (JT.mem_normalizer_of_conj_mem fun e he => ?_)
    rw [Subgroup.mem_centralizer_iff.mp (s.fr.E_le_CS he) t (hT₁S ht), mul_inv_cancel_right]
    exact he
  have h2' : Nat.card ((s.fr.A T₂ ⊔ s.fr.E) ⊔ T₁ : Subgroup G) ∣
      Nat.card (s.fr.A T₂ ⊔ s.fr.E : Subgroup G) * 2 := by
    rw [← hT₁2]
    exact Dvd.intro _ (card_sup_mul_card_inf_of_le_normalizer hT₁N)
  have hYC : T₁ ⊔ s.fr.A T₂ ⊔ s.fr.E ≤ Subgroup.centralizer (s.fr.V T₂ : Set G) := by
    rw [← hC.1]
    exact le_sup_right
  have h3 : Nat.card (Subgroup.centralizer (s.fr.V T₂ : Set G)) ∣
      4 * Nat.card (T₁ ⊔ s.fr.A T₂ ⊔ s.fr.E : Subgroup G) := by
    rw [← hC.1, ← s.fr.card_V hT₂ h2]
    exact Dvd.intro _ (card_sup_mul_card_inf_of_le_normalizer
      (hYC.trans (Subgroup.centralizer_le_normalizer _)))
  have hUN : U ≤ Subgroup.normalizer
      (Subgroup.centralizer (s.fr.V T₂ : Set G) : Set G) := by
    have : U ≤ Subgroup.normalizer (s.fr.V T₂ : Set G) := by rw [hNV]; exact le_sup_left
    exact this.trans (normalizer_le_normalizer_centralizer _)
  have h4 : Nat.card (Subgroup.normalizer (s.fr.V T₂ : Set G)) ∣
      Nat.card (Subgroup.centralizer (s.fr.V T₂ : Set G)) * 3 := by
    rw [hNV, sup_comm, ← hU3]
    exact Dvd.intro _ (card_sup_mul_card_inf_of_le_normalizer hUN)
  rw [sup_aux4] at h3
  calc Nat.card (Subgroup.normalizer (s.fr.V T₂ : Set G))
      ∣ Nat.card (Subgroup.centralizer (s.fr.V T₂ : Set G)) * 3 := h4
    _ ∣ (4 * Nat.card ((s.fr.A T₂ ⊔ s.fr.E) ⊔ T₁ : Subgroup G)) * 3 := Nat.mul_dvd_mul_right h3 _
    _ ∣ (4 * (Nat.card (s.fr.A T₂ ⊔ s.fr.E : Subgroup G) * 2)) * 3 :=
        Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_left _ h2') _
    _ ∣ (4 * ((Nat.card (s.fr.A T₂) * Nat.card s.fr.E) * 2)) * 3 :=
        Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_left _ (Nat.mul_dvd_mul_right h1 _)) _
    _ = 24 * (Nat.card (s.fr.A T₂) * Nat.card s.fr.E) := by ring


end Std

end CFSG.Walter.W67
