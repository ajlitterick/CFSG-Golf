module

public import CFSG.Monster.Existence.TwoPoint.CoPairOrbit

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.CoPair

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.Existence.Co2Bridge
  CFSG.Monster.Existence.CoPair.Native

attribute [local instance] kvLeft

section Generic

variable {G X : Type*} [Group G] [MulAction G X]

theorem exists_equivariant_hom {n : ℕ} {Ω : Set X} (hΩ : Ω.Finite) (p : X → Fin n)
    (hp : ∀ j : Fin n, ∃ x ∈ Ω, p x = j) (a b : G) (σa σb : Equiv.Perm (Fin n))
    (ha : ∀ x ∈ Ω, a • x ∈ Ω ∧ p (a • x) = σa (p x))
    (hb : ∀ x ∈ Ω, b • x ∈ Ω ∧ p (b • x) = σb (p x)) :
    ∃ Φ : Subgroup.closure ({a, b} : Set G) →* Equiv.Perm (Fin n),
      Φ ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩ = σa ∧
      Φ ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩ = σb := by
  classical
  let D : Subgroup G :=
    { carrier := {g | (∀ x ∈ Ω, g • x ∈ Ω) ∧
        ∃ σ : Equiv.Perm (Fin n), ∀ x ∈ Ω, p (g • x) = σ (p x)}
      one_mem' := ⟨fun x hx => by simpa using hx, 1, fun x _ => by simp⟩
      mul_mem' := fun {g h} hg hh => by
        refine ⟨fun x hx => ?_, ?_⟩
        · rw [mul_smul]
          exact hg.1 _ (hh.1 x hx)
        · obtain ⟨σ, hσ⟩ := hg.2
          obtain ⟨τ, hτ⟩ := hh.2
          refine ⟨σ * τ, fun x hx => ?_⟩
          rw [mul_smul, hσ _ (hh.1 x hx), hτ x hx]
          rfl
      inv_mem' := fun {g} hg => by
        have hinv : ∀ x ∈ Ω, g⁻¹ • x ∈ Ω := fun x hx => by
          have : g ∈ VisCert.invSubgroup Ω hΩ := hg.1
          exact (VisCert.invSubgroup Ω hΩ).inv_mem this x hx
        refine ⟨hinv, ?_⟩
        obtain ⟨σ, hσ⟩ := hg.2
        refine ⟨σ⁻¹, fun x hx => ?_⟩
        have h1 := hσ (g⁻¹ • x) (hinv x hx)
        rw [smul_inv_smul] at h1
        rw [h1]
        simp }
  have haD : a ∈ D := ⟨fun x hx => (ha x hx).1, σa, fun x hx => (ha x hx).2⟩
  have hbD : b ∈ D := ⟨fun x hx => (hb x hx).1, σb, fun x hx => (hb x hx).2⟩
  have hle : Subgroup.closure ({a, b} : Set G) ≤ D :=
    (Subgroup.closure_le _).2 (by rintro _ (rfl | rfl) <;> assumption)
  have huniq : ∀ (g : G) (σ τ : Equiv.Perm (Fin n)), (∀ x ∈ Ω, p (g • x) = σ (p x)) →
      (∀ x ∈ Ω, p (g • x) = τ (p x)) → σ = τ := by
    intro g σ τ h1 h2
    ext j
    obtain ⟨x, hx, rfl⟩ := hp j
    rw [← h1 x hx, ← h2 x hx]
  let φ : Subgroup.closure ({a, b} : Set G) → Equiv.Perm (Fin n) :=
    fun g => Classical.choose (hle g.2).2
  have hφ : ∀ (g : Subgroup.closure ({a, b} : Set G)), ∀ x ∈ Ω,
      p ((g : G) • x) = φ g (p x) := fun g => Classical.choose_spec (hle g.2).2
  refine ⟨{ toFun := φ, map_one' := ?_, map_mul' := ?_ }, ?_, ?_⟩
  · exact huniq ((1 : Subgroup.closure ({a, b} : Set G)) : G) _ 1 (hφ 1) (fun x _ => by simp)
  · intro g h
    refine huniq ((g * h : Subgroup.closure ({a, b} : Set G)) : G) _ (φ g * φ h) (hφ _)
      fun x hx => ?_
    rw [Subgroup.coe_mul, mul_smul, hφ g _ ((hle h.2).1 x hx), hφ h x hx]
    rfl
  · exact huniq a _ σa (hφ ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩)
      (fun x hx => (ha x hx).2)
  · exact huniq b _ σb (hφ ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩)
      (fun x hx => (hb x hx).2)

theorem range_eq_closure {a b : G} {n : ℕ} {σa σb : Equiv.Perm (Fin n)}
    (Φ : Subgroup.closure ({a, b} : Set G) →* Equiv.Perm (Fin n))
    (h1 : Φ ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩ = σa)
    (h2 : Φ ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩ = σb) :
    Φ.range = Subgroup.closure {σa, σb} := by
  apply le_antisymm
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [h1]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [h2]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    | one => exact (Φ.map_one ▸ Subgroup.one_mem _ : Φ 1 ∈ _)
    | mul x y hx hy ihx ihy =>
      have := Subgroup.mul_mem _ ihx ihy
      rwa [← map_mul] at this
    | inv x hx ih =>
      have := Subgroup.inv_mem _ ih
      rwa [← map_inv] at this
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, h1⟩
    · exact ⟨_, h2⟩

end Generic


end CFSG.Monster.Existence.CoPair
