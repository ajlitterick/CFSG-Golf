module

public import CFSG.ClassicalInvolution.Balance.Delta

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification

section Constant

variable {G : Type*} [Group G]


@[expose] def StronglyBalanced (A : Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → involutionOddCore a ≤ Subgroup.centralizer (A : Set G)


end Constant

section Equivariance

variable {G : Type*} [Group G]

theorem exists_map_four {A F' : Subgroup G} (g : G)
    (hF' : F' ∈ signalizerFunctorEk 2 2 (A.map (MulAut.conj g).toMonoidHom)) :
    ∃ F ∈ signalizerFunctorEk 2 2 A, F.map (MulAut.conj g).toMonoidHom = F' := by
  set e : G ≃* G := MulAut.conj g with he
  refine ⟨F'.map e.symm.toMonoidHom, ⟨fun y hy => ?_, ?_⟩, ?_⟩
  · obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    have := hF'.1 hy'
    rw [Subgroup.mem_map_equiv] at this
    exact this
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hF'.2
  · ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simp

theorem StronglyBalanced.map {A : Subgroup G} (h : StronglyBalanced A) (g : G) :
    StronglyBalanced (A.map (MulAut.conj g).toMonoidHom) := by
  intro a' ha' ha'1 x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
  have ha1 : a ≠ 1 := fun h1 => ha'1 (by simp [h1])
  have hx' : x ∈ (involutionOddCore a).map (MulAut.conj g).toMonoidHom := by
    rw [involutionOddCore_map]; exact hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx'
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨c, hc, rfl⟩
  have := Subgroup.mem_centralizer_iff.mp (h a ha ha1 hy) c hc
  change g * c * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * c * g⁻¹)
  calc g * c * g⁻¹ * (g * y * g⁻¹) = g * (c * y) * g⁻¹ := by group
    _ = g * (y * c) * g⁻¹ := by rw [this]
    _ = g * y * g⁻¹ * (g * c * g⁻¹) := by group


@[expose] def ShareFour (X Y : Subgroup G) : Prop :=
  ∃ F ∈ signalizerFunctorEk 2 2 X, F ∈ signalizerFunctorEk 2 2 Y

theorem ShareFour.symm {X Y : Subgroup G} (h : ShareFour X Y) : ShareFour Y X :=
  let ⟨F, hX, hY⟩ := h
  ⟨F, hY, hX⟩


end Equivariance

section Descent

variable {G : Type*} [Group G]

theorem normal_of_constant_on_connected {𝒯 : Set (Subgroup G)} (Φ : Subgroup G → Subgroup G)
    (r : Subgroup G → Subgroup G → Prop)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hequi : ∀ A ∈ 𝒯, ∀ g : G,
      (Φ A).map (MulAut.conj g).toMonoidHom = Φ (A.map (MulAut.conj g).toMonoidHom))
    (hr : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, r A A' → Φ A = Φ A')
    (hconn : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
      Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ r X Y) A A') :
    ∀ A ∈ 𝒯, (Φ A).Normal := by
  intro A hA
  have hconst : ∀ A', A' ∈ 𝒯 → Φ A = Φ A' := by
    intro A' hA'
    have hpath := hconn A hA A' hA'
    clear hA'
    induction hpath with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (hr _ hbc.1 _ hbc.2.1 hbc.2.2)
  refine ⟨fun n hn g => ?_⟩
  have h1 : g * n * g⁻¹ ∈ (Φ A).map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
  rwa [hequi A hA g, ← hconst _ (hinv A hA g)] at h1

theorem reflTransGen_symm_of_symm {α : Type*} {r : α → α → Prop} (hr : ∀ x y, r x y → r y x)
    {a b : α} (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (hr _ _ hbc) ih

end Descent

section Triviality

variable {G : Type} [Group G] [Finite G]


@[expose] def conjClass (A : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ g : G, X = A.map (MulAut.conj g).toMonoidHom}


end Triviality

end CFSG.ClassicalInvolution.Balance.Bootstrap
