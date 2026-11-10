module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {m : ℕ}

section Standard


end Standard

section Frame

theorem fin_zero_ne_one : (0 : Fin (m + 1 + 1)) ≠ 1 := fun h => by
  simpa using congrArg Fin.val h

structure IsSymplecticFrame (u₁ w₁ u₂ w₂ : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K) : Prop where
  h₁ : form u₁ w₁ = 1
  h₂ : form u₂ w₂ = 1
  o₁ : form u₁ u₂ = 0
  o₂ : form u₁ w₂ = 0
  o₃ : form w₁ u₂ = 0
  o₄ : form w₁ w₂ = 0

@[expose] def CarriesFrame (g : StatedSp (m + 1 + 1) K)
    (u₁ w₁ u₂ w₂ : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K) : Prop :=
  mat _ K g *ᵥ Pi.single (Sum.inl 0) 1 = u₁ ∧ mat _ K g *ᵥ Pi.single (Sum.inr 0) 1 = w₁ ∧
    mat _ K g *ᵥ Pi.single (Sum.inl 1) 1 = u₂ ∧ mat _ K g *ᵥ Pi.single (Sum.inr 1) 1 = w₂

variable {u₁ w₁ u₂ w₂ : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K}

theorem IsSymplecticFrame.exists_carries (hq : IsSymplecticFrame u₁ w₁ u₂ w₂) :
    ∃ g : StatedSp (m + 1 + 1) K, CarriesFrame g u₁ w₁ u₂ w₂ :=
  exists_sp_apply_eq_two u₁ w₁ u₂ w₂ hq.h₁ hq.h₂ hq.o₁ hq.o₂ hq.o₃ hq.o₄

theorem CarriesFrame.inv_mul_mem {g g' : StatedSp (m + 1 + 1) K} (hg : CarriesFrame g u₁ w₁ u₂ w₂)
    (hg' : CarriesFrame g' u₁ w₁ u₂ w₂) :
    g⁻¹ * g' ∈ suppGroup (coords (0 : Fin (m + 1 + 1)) ∪ coords 1)ᶜ := by
  have hS : ParClosed (coords (0 : Fin (m + 1 + 1)) ∪ coords 1) := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl (parClosed_coords 0 a ha)
    · exact Or.inr (parClosed_coords 1 a ha)
  have key : ∀ t : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1), ∀ u : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K,
      mat _ K g *ᵥ Pi.single t 1 = u → mat _ K g' *ᵥ Pi.single t 1 = u →
        mat _ K (g⁻¹ * g') *ᵥ Pi.single t 1 = Pi.single t 1 := fun t u h h' => by
    rw [map_mul, ← Matrix.mulVec_mulVec, h']
    exact ((mulVec_eq_iff g _ _).1 h).symm
  rw [mem_suppGroup_iff hS.compl]
  intro t ht r
  have ht' : t ∈ coords (0 : Fin (m + 1 + 1)) ∪ coords 1 := by
    by_contra h'
    exact ht h'
  have hmv : mat _ K (g⁻¹ * g') *ᵥ Pi.single t 1 = Pi.single t 1 := by
    rcases ht' with ht' | ht'
    · rcases mem_coords.1 ht' with rfl | rfl
      · exact key _ _ hg.1 hg'.1
      · exact key _ _ hg.2.1 hg'.2.1
    · rcases mem_coords.1 ht' with rfl | rfl
      · exact key _ _ hg.2.2.1 hg'.2.2.1
      · exact key _ _ hg.2.2.2 hg'.2.2.2
  have := congrFun hmv r
  rw [mulVec_single_one_apply] at this
  rw [this, Pi.single_apply, Matrix.one_apply]


theorem CarriesFrame.mulVec_conj_shortBlock {g : StatedSp (m + 1 + 1) K}
    (hg : CarriesFrame g u₁ w₁ u₂ w₂) (A : SL(2, K)) :
    mat _ K (g * shortBlock K (fin_zero_ne_one (m := m)) A * g⁻¹) *ᵥ u₁ =
        (A : Matrix (Fin 2) (Fin 2) K) 0 0 • u₁ + (A : Matrix (Fin 2) (Fin 2) K) 1 0 • u₂ ∧
      mat _ K (g * shortBlock K (fin_zero_ne_one (m := m)) A * g⁻¹) *ᵥ u₂ =
        (A : Matrix (Fin 2) (Fin 2) K) 0 1 • u₁ + (A : Matrix (Fin 2) (Fin 2) K) 1 1 • u₂ ∧
      mat _ K (g * shortBlock K (fin_zero_ne_one (m := m)) A * g⁻¹) *ᵥ w₁ =
        ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 • w₁ +
          ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 1 • w₂ ∧
      mat _ K (g * shortBlock K (fin_zero_ne_one (m := m)) A * g⁻¹) *ᵥ w₂ =
        ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 0 • w₁ +
          ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1 • w₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
  have conjact : ∀ v : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K,
      mat _ K (g * shortBlock K (fin_zero_ne_one (m := m)) A * g⁻¹) *ᵥ (mat _ K g *ᵥ v) =
        mat _ K g *ᵥ (mat _ K (shortBlock K (fin_zero_ne_one (m := m)) A) *ᵥ v) := fun v => by
    have e : mat _ K (g * shortBlock K (fin_zero_ne_one (m := m)) A * g⁻¹) *ᵥ (mat _ K g *ᵥ v) =
        mat _ K g *ᵥ (mat _ K (shortBlock K (fin_zero_ne_one (m := m)) A) *ᵥ
          (mat _ K g⁻¹ *ᵥ (mat _ K g *ᵥ v))) := by
      simp only [map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e, mulVec_inv_mulVec]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h1, conjact, shortBlock_mulVec_inl_left, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, h1, h3]
  · rw [← h3, conjact, shortBlock_mulVec_inl_right, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, h1, h3]
  · rw [← h2, conjact, shortBlock_mulVec_inr_left, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, h2, h4]
  · rw [← h4, conjact, shortBlock_mulVec_inr_right, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, h2, h4]

theorem CarriesFrame.planeGroup_pair_two {g : StatedSp (m + 1 + 1) K}
    (hg : CarriesFrame g u₁ w₁ u₂ w₂) :
    planeGroup (Submodule.span K {u₂, w₂}) =
      (longRootSp2 K (m + 1 + 1) 1).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨-, -, h3, h4⟩ := hg
  rw [← h3, ← h4, planeGroup_span_conj, ← planeGroup_stdPlane]
  rfl


end Frame

end CFSG.ClassicalInvolution.Models.SymplecticPairs
