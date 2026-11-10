module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Cell
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

@[expose] def fixSub {Y : Type} [Group Y] (α : MulAut Y) : Subgroup Y :=
  α.toMonoidHom.eqLocus (MonoidHom.id Y)

theorem mem_fixSub {Y : Type} [Group Y] {α : MulAut Y} {s : Y} : s ∈ fixSub α ↔ α s = s := Iff.rfl

@[expose] def OutAbelian (Y : Type) [Group Y] : Prop :=
  ∀ α β : MulAut Y, α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : Y →* MulAut Y).range

theorem outAbelian_of_hom {Y E : Type} [Group Y] [Group E] (Θ : MulAut Y →* E)
    (hcomm : ∀ a b : E, a * b = b * a) (hker : Θ.ker = (MulAut.conj : Y →* MulAut Y).range) :
    OutAbelian Y := by
  intro α β
  rw [← hker, MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  rw [hcomm (Θ α) (Θ β)]
  group

theorem outAbelian_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : OutAbelian Y) :
    OutAbelian Y' := by
  intro α β
  have h1 := h (MulAut.congr e.symm α) (MulAut.congr e.symm β)
  obtain ⟨g, hg⟩ := h1
  refine ⟨e g, ?_⟩
  have key : ∀ γ : MulAut Y, MulAut.congr e γ = e.symm.trans (γ.trans e) := fun γ => rfl
  ext y
  have := congrArg (fun σ : MulAut Y => e (σ (e.symm y))) hg
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply] at this ⊢
  simpa [map_mul, map_inv] using this

theorem comm_mem_sup_centralizer {A : Type} [Group A] (K : Subgroup A) [K.Normal]
    (hOut : OutAbelian ↥K) (a b : A) : ⁅a, b⁆ ∈ K ⊔ centralizer (K : Set A) := by
  let ρ : A →* MulAut ↥K := MulAut.conjNormal
  obtain ⟨k, hk⟩ := hOut (ρ a) (ρ b)
  have hρ : ρ ⁅a, b⁆ = ρ a * ρ b * (ρ a)⁻¹ * (ρ b)⁻¹ := by
    simp only [commutatorElement_def, map_mul, map_inv]
  have hc : (k : A)⁻¹ * ⁅a, b⁆ ∈ centralizer (K : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun σ : MulAut ↥K => ((σ ⟨y, hy⟩ : ↥K) : A)) (hk.trans hρ.symm)
    simp only [MulAut.conj_apply] at h1
    have h2 : (k : A) * y * (k : A)⁻¹ = ⁅a, b⁆ * y * ⁅a, b⁆⁻¹ := h1
    calc y * ((k : A)⁻¹ * ⁅a, b⁆) = (k : A)⁻¹ * ((k : A) * y * (k : A)⁻¹) * ⁅a, b⁆ := by group
      _ = (k : A)⁻¹ * (⁅a, b⁆ * y * ⁅a, b⁆⁻¹) * ⁅a, b⁆ := by rw [h2]
      _ = (k : A)⁻¹ * ⁅a, b⁆ * y := by group
  have : ⁅a, b⁆ = (k : A) * ((k : A)⁻¹ * ⁅a, b⁆) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right hc)

theorem false_of_coatom_subgroup {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnonab : ∃ a b : T, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] {M : Subgroup T} (hco : IsCoatom M)
    (hOp : ∀ Y : Subgroup T, Y ≤ M → (∀ c ∈ M, ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) → IsPGroup p ↥Y → Y = ⊥)
    {X : Subgroup T} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hN : M ≤ normalizer (X : Set T)) : False := by
  classical
  have hXN : X ≤ normalizer (X : Set T) := Subgroup.le_normalizer
  rcases (hco.le_iff).mp hN with hNtop | hNC
  · have hXn : X.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with h | h
    · exact hX1 h
    · have hT : IsPGroup p T := by
        have : IsPGroup p ↥(⊤ : Subgroup T) := h ▸ hX
        exact this.of_equiv Subgroup.topEquiv
      have : Nontrivial T := by
        obtain ⟨a, b, hab⟩ := hnonab
        exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
      have hcn : Nontrivial (center T) := hT.center_nontrivial
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center T) with h1 | h1
      · obtain ⟨x, hx⟩ := exists_ne (1 : center T)
        exact hx (Subtype.ext ((Subgroup.eq_bot_iff_forall (center T)).mp h1 x x.2))
      · obtain ⟨a, b, hab⟩ := hnonab
        have : a ∈ center T := by rw [h1]; exact mem_top a
        exact hab ((Subgroup.mem_center_iff.mp this b).symm)
  · have hXC : X ≤ M := hNC ▸ hXN
    refine hX1 (hOp X hXC ?_ hX)
    intro c hc y hy
    have hcN : c ∈ normalizer (X : Set T) := by rw [hNC]; exact hc
    exact (Subgroup.mem_normalizer_iff.mp hcN y).mp hy

@[expose] def InvolFact {Y : Type} [Group Y] (α : MulAut Y) : Prop :=
  (IsCoatom (fixSub α) ∧ ∀ N : Subgroup Y, N ≤ fixSub α → (∀ c ∈ fixSub α, ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
      Odd (Nat.card ↥N) → N = ⊥) ∨
    (∃ T : Subgroup Y, T ≤ fixSub α ∧ IsSimpleGroup ↥T ∧ (∃ a b : ↥T, a * b ≠ b * a) ∧
      ∀ k : Kind, ¬ KindFactor k ↥T)


theorem odd_card_of_isPGroup_odd_prime {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : IsPGroup p Y) : Odd (Nat.card Y) := by
  obtain ⟨n, hn⟩ := h.exists_card_eq
  rw [hn]
  exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow

theorem isPerfect_of_simple_nonab {T : Type} [Group T] [IsSimpleGroup T]
    (hnonab : ∃ a b : T, a * b ≠ b * a) : Group.IsPerfect T := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator T) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have h1 : ⁅a, b⁆ ∈ commutator T := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_def] at h1
    apply hab
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  · exact h


end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
