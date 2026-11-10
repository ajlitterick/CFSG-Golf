module

public import CFSG.LieType.SemisimpleCentralizers.HeldLinearComponents

public section

namespace CFSG.LieType.SemisimpleCentralizers.Held

open CFSG.Open CFSG.Open.StatedAPI Matrix
open scoped commutatorElement

section Unitary

@[expose] def heldGU (a : ℕ) (M : Type) [Field M] (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x) :
    Subgroup (GL (Fin a) M) where
  carrier := {A | ((A : Matrix (Fin a) (Fin a) M).map τ)ᵀ * (A : Matrix (Fin a) (Fin a) M) = 1}
  mul_mem' := by
    intro A B hA hB
    have hA' : ((A : Matrix (Fin a) (Fin a) M).map τ)ᵀ * (A : Matrix (Fin a) (Fin a) M) = 1 := hA
    have hB' : ((B : Matrix (Fin a) (Fin a) M).map τ)ᵀ * (B : Matrix (Fin a) (Fin a) M) = 1 := hB
    have hmapmul : ∀ X Y : Matrix (Fin a) (Fin a) M, (X * Y).map τ = X.map τ * Y.map τ :=
      fun X Y => Matrix.map_mul (f := τ.toRingHom)
    show ((((A * B : GL (Fin a) M)) : Matrix (Fin a) (Fin a) M).map τ)ᵀ *
      ((A * B : GL (Fin a) M) : Matrix (Fin a) (Fin a) M) = 1
    rw [Units.val_mul, hmapmul, Matrix.transpose_mul, mul_assoc,
      ← mul_assoc (((A : Matrix (Fin a) (Fin a) M).map τ)ᵀ), hA', one_mul, hB']
  one_mem' := by
    show (((1 : GL (Fin a) M) : Matrix (Fin a) (Fin a) M).map τ)ᵀ *
      ((1 : GL (Fin a) M) : Matrix (Fin a) (Fin a) M) = 1
    rw [Units.val_one, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one,
      Matrix.one_mul]
  inv_mem' := by
    intro A hA
    have hA' : ((A : Matrix (Fin a) (Fin a) M).map τ)ᵀ * (A : Matrix (Fin a) (Fin a) M) = 1 := hA
    show ((((A⁻¹ : GL (Fin a) M)) : Matrix (Fin a) (Fin a) M).map τ)ᵀ *
      ((A⁻¹ : GL (Fin a) M) : Matrix (Fin a) (Fin a) M) = 1
    rw [Matrix.coe_units_inv]
    have hNinv := Matrix.inv_eq_left_inv hA'
    have hNN : (A : Matrix (Fin a) (Fin a) M) * (A : Matrix (Fin a) (Fin a) M)⁻¹ = 1 := by
      rw [← Matrix.coe_units_inv]
      exact Units.mul_inv A
    have hmap : ((A : Matrix (Fin a) (Fin a) M)⁻¹).map τ = (A : Matrix (Fin a) (Fin a) M)ᵀ := by
      rw [hNinv, Matrix.transpose_map, Matrix.map_map]
      have hid : (⇑τ ∘ ⇑τ) = id := funext hτ
      rw [hid, Matrix.map_id]
    rw [hmap, Matrix.transpose_transpose]
    exact hNN

theorem mem_heldGU {a : ℕ} {M : Type} [Field M] {τ : M ≃+* M} {hτ : ∀ x, τ (τ x) = x}
    {A : GL (Fin a) M} :
    A ∈ heldGU a M τ hτ ↔ ((A : Matrix (Fin a) (Fin a) M).map τ)ᵀ * (A : Matrix (Fin a) (Fin a) M) = 1 :=
  Iff.rfl

@[expose] def heldSU (a : ℕ) (M : Type) [Field M] (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x) :
    Subgroup (GL (Fin a) M) :=
  heldGU a M τ hτ ⊓ StatedSL a M

theorem commutatorElement_mem_heldSU {a : ℕ} {M : Type} [Field M] {τ : M ≃+* M}
    {hτ : ∀ x, τ (τ x) = x} {x y : GL (Fin a) M} (hx : x ∈ heldGU a M τ hτ)
    (hy : y ∈ heldGU a M τ hτ) : ⁅x, y⁆ ∈ heldSU a M τ hτ := by
  refine Subgroup.mem_inf.mpr ⟨?_, commutatorElement_mem_statedSL x y⟩
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

theorem mul_comm_GL_of_le_one {M : Type} [Field M] {a : ℕ} (ha : a ≤ 1) (x y : GL (Fin a) M) :
    x * y = y * x := by
  interval_cases a
  · exact Units.ext (Subsingleton.elim _ _)
  · apply Units.ext
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, mul_comm]

end Unitary

theorem not_isQuasisimple_of_mulEquiv {Γ Γ' : Type*} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
    (h : ∀ x y : Γ', x * y = y * x) : ¬ CFSG.Open.IsQuasisimple Γ :=
  not_isQuasisimple_of_comm fun x y => e.injective (by rw [map_mul, map_mul]; exact h _ _)

theorem comap_equiv_of_injective_le_range {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (T : Subgroup G') (hT : T ≤ f.range) :
    Nonempty (↥(T.comap f) ≃* ↥T) :=
  ⟨(Subgroup.equivMapOfInjective (T.comap f) f hf).trans
    (MulEquiv.subgroupCongr (by rw [Subgroup.map_comap_eq, inf_eq_right.mpr hT]))⟩

theorem triv_comap {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (T : Subgroup G') (hT : T ≤ f.range)
    (hTt : ∀ X : Subgroup T, CFSG.Open.IsComponentOf X ⊤ → X = ⊤) :
    ∀ X : Subgroup (T.comap f), CFSG.Open.IsComponentOf X ⊤ → X = ⊤ := by
  intro X hX
  obtain ⟨e⟩ := comap_equiv_of_injective_le_range f hf T hT
  have hXe := (CFSG.ComponentClassification.LocalComponents.equiv_iff e X).2 hX
  exact eq_top_of_map_equiv_eq_top e X (hTt _ hXe)

@[expose] def SUComponentsTrivial : Prop :=
  ∀ (a Q : ℕ) (M : Type) [Field M] [Finite M] (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x),
    Nat.card M = Q ^ 2 → (∀ x, τ x = x ^ Q) →
      ∀ X : Subgroup (heldSU a M τ hτ), IsComponentOf X ⊤ → X = ⊤

@[expose] def UnitaryOrLinearBlock (Q : ℕ) (Γ : Type) [Group Γ] : Prop :=
  (∃ (a d : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x),
      Odd d ∧ (∀ x : M, τ x = x ^ (Q ^ d)) ∧ Nat.card M = (Q ^ d) ^ 2 ∧
        Nonempty (Γ ≃* heldGU a M τ hτ)) ∨
  (∃ (b e : ℕ) (M : Type) (_ : Field M) (_ : Finite M),
      Nat.card M = Q ^ (2 * e) ∧ Nonempty (Γ ≃* GL (Fin b) M))

@[expose] def UnitaryCentralizerDecomposition : Prop :=
  ∀ (Q n : ℕ) (L : Type) [Field L] [Finite L] (τ : L ≃+* L) (hτ : ∀ x, τ (τ x) = x)
    (s : GL (Fin n) L), Nat.card L = Q ^ 2 → (∀ x, τ x = x ^ Q) → s ∈ heldSU n L τ hτ →
      (orderOf s : L) ≠ 0 →
      ∃ (r : ℕ) (H : Fin r → Type) (_ : ∀ k, Group (H k)) (_ : ∀ k, Finite (H k)),
        (∀ k, UnitaryOrLinearBlock Q (H k)) ∧
          Nonempty (↥(Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ) ≃*
            ∀ k, H k)

theorem mulSingle_injective' {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] (i : ι) :
    Function.Injective (MonoidHom.mulSingle H i) := fun a b hab => by
  have := congrFun hab i
  simpa [MonoidHom.mulSingle_apply] using this

theorem component_eq_factor_image {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type}
    [∀ i, Group (H i)] [Finite ι] [∀ i, Finite (H i)] (S : ∀ i, Subgroup (H i))
    (hS : ∀ i (a b : H i), ⁅a, b⁆ ∈ S i)
    (hSt : ∀ i (X : Subgroup (S i)), IsComponentOf X ⊤ → X = ⊤)
    {J : Subgroup (∀ j, H j)} (hJ : IsComponentOf J ⊤) :
    ∃ i, J = (S i).map (MonoidHom.mulSingle H i) := by
  obtain ⟨i, hi⟩ := exists_factor_of_isComponentOf_top (H := H) hJ
  refine ⟨i, ?_⟩
  have hle : J ≤ (S i).map (MonoidHom.mulSingle H i) := by
    have h1 := commutator_eq_self_of_isComponentOf_top hJ
    have h2 := Subgroup.commutator_mono hi hi
    rw [h1] at h2
    exact h2.trans (commutator_factorSub_le (H := H) (S i) (hS i))
  have hms := mulSingle_injective' (H := H) i
  have hX : IsComponentOf (J.subgroupOf ((S i).map (MonoidHom.mulSingle H i))) ⊤ :=
    CFSG.ComponentClassification.LocalComponents.of_overgroup hJ hle
  let e : ↥((S i).map (MonoidHom.mulSingle H i)) ≃* ↥(S i) :=
    (Subgroup.equivMapOfInjective (S i) (MonoidHom.mulSingle H i) hms).symm
  have hXe := (CFSG.ComponentClassification.LocalComponents.equiv_iff e _).2 hX
  have htop := hSt i _ hXe
  have hXtop := eq_top_of_map_equiv_eq_top e _ htop
  exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp hXtop)


end CFSG.LieType.SemisimpleCentralizers.Held

end
