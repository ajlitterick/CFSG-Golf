module

public import CFSG.ClassicalInvolution.AschTight.S1916Basic
public import CFSG.ClassicalInvolution.AschTight.S1916Wreath

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G]

theorem IsQuaternionSub.mul_self_eq_one_of_central {P : Subgroup G} (hP : IsQuaternionSub P)
    {q : G} (hq : q ∈ P) (hc : ∀ y ∈ P, q * y = y * q) : q * q = 1 := by
  obtain ⟨a, b, ha4, -, hb2, hbab, hcl⟩ := hP
  have haP : a ∈ P := hcl ▸ Subgroup.subset_closure (by simp)
  have hbP : b ∈ P := hcl ▸ Subgroup.subset_closure (by simp)
  have hconj : ∀ i : ℤ, b * a ^ i * b⁻¹ = a ^ (-i) := fun i => by
    rw [← _root_.conj_zpow, hbab, inv_zpow']
  have hconj' : ∀ i : ℤ, b⁻¹ * a ^ i * b = a ^ (-i) := fun i => by
    have h1 := hconj (-i)
    rw [neg_neg] at h1
    calc b⁻¹ * a ^ i * b = b⁻¹ * (b * a ^ (-i) * b⁻¹) * b := by rw [h1]
      _ = a ^ (-i) := by group
  have hbN : b ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [hconj]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
    · intro hw
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hw
      have e : w = b⁻¹ * a ^ i * b := by rw [hi]; group
      rw [e, hconj']
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
  have hq' : q ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
    rw [← closure_pair_eq_sup_zpowers, hcl]
    exact hq
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (Subgroup.zpowers_le.mpr hbN)] at hq'
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hq'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hb2' : b ^ (2 : ℤ) = a ^ ((orderOf a / 2 : ℕ) : ℤ) := by
    rw [zpow_two, hb2, zpow_natCast]
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  ·
    have hqa : a ^ i * b ^ (m + m) = a ^ (i + ((orderOf a / 2 : ℕ) : ℤ) * m) := by
      rw [← two_mul, zpow_mul, hb2', ← zpow_mul, ← zpow_add]
    rw [hqa]
    set j : ℤ := i + ((orderOf a / 2 : ℕ) : ℤ) * m
    have h1 := hc b hbP
    rw [hqa] at h1
    have h2 : a ^ (-j) = a ^ j := by
      rw [← hconj j]
      calc b * a ^ j * b⁻¹ = a ^ j * b * b⁻¹ := by rw [← h1]
        _ = a ^ j := by group
    calc a ^ j * a ^ j = a ^ j * a ^ (-j) := by rw [h2]
      _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
  ·
    exfalso
    have hqa : a ^ i * b ^ (2 * m + 1) = a ^ (i + ((orderOf a / 2 : ℕ) : ℤ) * m) * b := by
      rw [zpow_add_one, zpow_mul, hb2', ← zpow_mul, ← mul_assoc, ← zpow_add]
    set j : ℤ := i + ((orderOf a / 2 : ℕ) : ℤ) * m
    have h1 := hc a haP
    rw [hqa] at h1
    have h2 : a ^ j * (b * a * b⁻¹) = a * a ^ j := by
      calc a ^ j * (b * a * b⁻¹) = a ^ j * b * a * b⁻¹ := by group
        _ = a * (a ^ j * b) * b⁻¹ := by rw [h1]
        _ = a * a ^ j := by group
    rw [hbab] at h2
    have h3 : a⁻¹ = a := by
      have e1 : a ^ j * a⁻¹ = a ^ j * a := by
        rw [h2, ← zpow_one_add, ← zpow_add_one, add_comm]
      exact mul_left_cancel e1
    have h4 : a ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← h3]
      exact inv_mul_cancel a
    have h5 := orderOf_dvd_of_pow_eq_one h4
    have := Nat.le_of_dvd (by norm_num) h5
    omega

theorem natCard_eq_of_isSylow2In [Finite G] {P H : Subgroup G} (hP : IsSylow2In P H) :
    Nat.card P = 2 ^ (Nat.card H).factorization 2 := by
  have h1 := Sylow.card_eq_multiplicity (sylowOf hP)
  rw [coe_sylowOf] at h1
  rw [← h1]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv).symm

theorem mem_normalizer_sup {A B : Subgroup G} {c : G} (hA : c ∈ Subgroup.normalizer (A : Set G))
    (hB : c ∈ Subgroup.normalizer (B : Set G)) :
    c ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hA hB ⊢
  rw [conjSub, Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) hA hB

theorem mem_normalizer_inf {A B : Subgroup G} {c : G} (hA : c ∈ Subgroup.normalizer (A : Set G))
    (hB : c ∈ Subgroup.normalizer (B : Set G)) :
    c ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hA hB ⊢
  rw [conjSub, Subgroup.map_inf_eq A B (MulAut.conj c).toMonoidHom (MulAut.conj c).injective]
  exact congrArg₂ (· ⊓ ·) hA hB

theorem inf_sup_eq_sup_inf [Finite G] (S : Sylow 2 G) {C H₁ H₂ : Subgroup G}
    (hSC : (S : Subgroup G) ≤ C) (h₁C : H₁ ≤ C) (h₂C : H₂ ≤ C)
    (hn₁ : C ≤ Subgroup.normalizer (H₁ : Set G)) (hn₂ : C ≤ Subgroup.normalizer (H₂ : Set G)) :
    (S : Subgroup G) ⊓ (H₁ ⊔ H₂) = ((S : Subgroup G) ⊓ H₁) ⊔ ((S : Subgroup G) ⊓ H₂) := by
  refine le_antisymm ?_ (sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right))
  set P₁ := (S : Subgroup G) ⊓ H₁
  set P₂ := (S : Subgroup G) ⊓ H₂
  have hP₁ := isSylow2In_inf S hSC h₁C hn₁
  have hP₂ := isSylow2In_inf S hSC h₂C hn₂
  have h₁₂C : H₁ ⊓ H₂ ≤ C := inf_le_left.trans h₁C
  have hn₁₂ : C ≤ Subgroup.normalizer ((H₁ ⊓ H₂ : Subgroup G) : Set G) :=
    fun c hc => mem_normalizer_inf (hn₁ hc) (hn₂ hc)
  have hP₁₂ := isSylow2In_inf S hSC h₁₂C hn₁₂
  have hMC : H₁ ⊔ H₂ ≤ C := sup_le h₁C h₂C
  have hnM : C ≤ Subgroup.normalizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) :=
    fun c hc => mem_normalizer_sup (hn₁ hc) (hn₂ hc)
  have hPM := isSylow2In_inf S hSC hMC hnM
  have hH := card_sup_mul_card_inf (A := H₁) (C := H₂) (h₂C.trans hn₁)
  have hP₂N : P₂ ≤ Subgroup.normalizer (P₁ : Set G) := by
    intro x hx
    have hx1 : x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
      Subgroup.le_normalizer hx.1
    exact mem_normalizer_inf hx1 (hn₁ (h₂C hx.2))
  have hP := card_sup_mul_card_inf hP₂N
  have hinf : P₁ ⊓ P₂ = (S : Subgroup G) ⊓ (H₁ ⊓ H₂) := by
    rw [inf_inf_inf_comm, inf_idem]
  rw [hinf, natCard_eq_of_isSylow2In hP₁, natCard_eq_of_isSylow2In hP₂,
    natCard_eq_of_isSylow2In hP₁₂] at hP
  have hfac := congrArg (fun n => n.factorization 2) hH
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hfac
  simp only [Finsupp.add_apply] at hfac
  have hcard : Nat.card ↥(P₁ ⊔ P₂) = 2 ^ (Nat.card ↥(H₁ ⊔ H₂)).factorization 2 := by
    have h1 : Nat.card ↥(P₁ ⊔ P₂) * 2 ^ (Nat.card ↥(H₁ ⊓ H₂)).factorization 2 =
        2 ^ (Nat.card ↥(H₁ ⊔ H₂)).factorization 2 *
          2 ^ (Nat.card ↥(H₁ ⊓ H₂)).factorization 2 := by
      rw [hP, ← pow_add, ← pow_add, hfac]
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  have hle : P₁ ⊔ P₂ ≤ (S : Subgroup G) ⊓ (H₁ ⊔ H₂) :=
    sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
  have hge : Nat.card ↥((S : Subgroup G) ⊓ (H₁ ⊔ H₂)) ≤ Nat.card ↥(P₁ ⊔ P₂) := by
    rw [natCard_eq_of_isSylow2In hPM, hcard]
  exact (Subgroup.eq_of_le_of_card_ge hle hge).ge


theorem le_oddCoreOf_of_odd [Finite G] {H N : Subgroup G} (hNH : N ≤ H)
    (hn : H ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf H := by
  have hnorm : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hn
  have hodd' : Odd (Nat.card ↥(N.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
  have hle : N.subgroupOf H ≤ classicalInvolutionOddCore ↥H := by
    unfold classicalInvolutionOddCore
    exact le_sSup ⟨hnorm, hodd'⟩
  intro x hx
  exact ⟨⟨x, hNH hx⟩, hle hx, rfl⟩

theorem exists_inner_of_mem_sup {R Q : Subgroup G} (hcomm : ∀ r ∈ R, ∀ q ∈ Q, r * q = q * r)
    {u : G} (hu : u ∈ R ⊔ Q) : ∃ q ∈ Q, ∀ y ∈ Q, u * y * u⁻¹ = q * y * q⁻¹ := by
  have hQN : Q ≤ Subgroup.normalizer (R : Set G) := fun q hq =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun r hr =>
      hcomm r hr q hq)
  have hu' : u ∈ ((R ⊔ Q : Subgroup G) : Set G) := hu
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R Q hQN] at hu'
  obtain ⟨r, hr, q, hq, rfl⟩ := Set.mem_mul.mp hu'
  refine ⟨q, hq, fun y hy => ?_⟩
  have hc : r * (q * y * q⁻¹) = (q * y * q⁻¹) * r :=
    hcomm r hr _ (Q.mul_mem (Q.mul_mem hq hy) (Q.inv_mem hq))
  calc r * q * y * (r * q)⁻¹ = r * (q * y * q⁻¹) * r⁻¹ := by group
    _ = q * y * q⁻¹ := by rw [hc]; group

theorem exists_inner_of_mem_sup' {R Q : Subgroup G} (hcomm : ∀ r ∈ R, ∀ q ∈ Q, r * q = q * r)
    {u : G} (hu : u ∈ R ⊔ Q) : ∃ r ∈ R, ∀ y ∈ R, u * y * u⁻¹ = r * y * r⁻¹ := by
  refine exists_inner_of_mem_sup (R := Q) (Q := R) (fun q hq r hr => (hcomm r hr q hq).symm) ?_
  rwa [sup_comm]


theorem exists_not_mem_of_isWreathed [Finite G] {S M V R Q : Subgroup G} {z : G}
    (hSM : ∀ u ∈ S, u ∈ M → u ∈ R ⊔ Q) (hcomm : ∀ r ∈ R, ∀ q ∈ Q, r * q = q * r)
    (hVS : V ≤ S) (hVN : V ≤ Subgroup.normalizer (R : Set G)) (hwr : IsWreathed (R ⊔ V))
    (hR2 : IsPGroup 2 R) (hz : IsUniqueInvolution R z)
    (hnc : ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x) : ∃ v ∈ V, v ∉ M := by
  by_contra hcon
  push Not at hcon
  refine not_forall_inner_of_isWreathed hwr le_sup_left hR2 hz hnc fun u hu => ?_
  have hu' : u ∈ ((R ⊔ V : Subgroup G) : Set G) := hu
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R V hVN] at hu'
  obtain ⟨r, hr, v, hv, rfl⟩ := Set.mem_mul.mp hu'
  obtain ⟨r', hr', hr'y⟩ := exists_inner_of_mem_sup' hcomm (hSM v (hVS hv) (hcon v hv))
  refine ⟨r * r', R.mul_mem hr hr', fun y hy => ?_⟩
  calc r * v * y * (r * v)⁻¹ = r * (v * y * v⁻¹) * r⁻¹ := by group
    _ = r * (r' * y * r'⁻¹) * r⁻¹ := by rw [hr'y y hy]
    _ = r * r' * y * (r * r')⁻¹ := by group


end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
