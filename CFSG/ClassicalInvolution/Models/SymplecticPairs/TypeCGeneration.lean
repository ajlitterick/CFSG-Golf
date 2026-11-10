module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Complement
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {n m : ℕ}

section Normal

theorem commutator_mul_central {G : Type*} [Group G] {a b z : G} (hz : z ∈ Subgroup.center G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ ∧ ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.1 hz
  constructor
  · rw [commutatorElement_def, commutatorElement_def]
    calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by rw [← h b]; group
  · rw [commutatorElement_def, commutatorElement_def]
    calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by rw [← h a⁻¹]; group

theorem scalars_le_center : (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) ≤
    Subgroup.center (StatedSp n K) := by
  intro g hg
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  simp only [Subgroup.coe_mul, ← hc]
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem eq_top_of_normal_of_not_le_center [Finite K] (hn : 1 ≤ n) (h4 : 4 ≤ Nat.card K)
    {N : Subgroup (StatedSp n K)} (hN : N.Normal) (hnc : ¬ N ≤ Subgroup.center (StatedSp n K)) :
    N = ⊤ := by
  have hsimple := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K n hn
    (Or.inl (Or.inr h4))
  have hperf : Group.IsPerfect (StatedSp n K) := by
    refine CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n K (Or.inl ?_)
    have := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  set Z := (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) with hZdef
  have hZ : Z ≤ Subgroup.center (StatedSp n K) := scalars_le_center
  have hmapN : (N.map (QuotientGroup.mk' Z)).Normal := hN.map _ (QuotientGroup.mk'_surjective Z)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Z)) with h | h
  · exfalso
    apply hnc
    intro x hx
    have hx' : QuotientGroup.mk' Z x ∈ N.map (QuotientGroup.mk' Z) := ⟨x, hx, rfl⟩
    rw [h] at hx'
    exact hZ ((QuotientGroup.eq_one_iff x).1 (by simpa using hx'))
  · have hsup : ∀ g : StatedSp n K, ∃ a ∈ N, ∃ z ∈ Z, g = a * z := by
      intro g
      have : QuotientGroup.mk' Z g ∈ N.map (QuotientGroup.mk' Z) := by rw [h]; trivial
      obtain ⟨a, ha, hag⟩ := this
      refine ⟨a, ha, a⁻¹ * g, QuotientGroup.eq.1 hag, by group⟩
    have hcomm : ∀ a b : StatedSp n K, ⁅a, b⁆ ∈ N := by
      intro a b
      obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := hsup a
      obtain ⟨b₁, hb₁, z₂, hz₂, rfl⟩ := hsup b
      rw [(commutator_mul_central (hZ hz₁)).1, (commutator_mul_central (hZ hz₂)).2]
      have : ⁅a₁, b₁⁆ = a₁ * (b₁ * a₁⁻¹ * b₁⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact mul_mem ha₁ (hN.conj_mem _ (inv_mem ha₁) _)
    have hcom : commutator (StatedSp n K) = ⊤ := Group.isPerfect_def.1 hperf
    have hle : ⁅(⊤ : Subgroup (StatedSp n K)), ⊤⁆ ≤ N :=
      Subgroup.commutator_le.2 fun a _ b _ => hcomm a b
    rw [← commutator_def, hcom] at hle
    exact eq_top_iff.2 hle

end Normal

section Orth


theorem noncomm_longBlock_transv (l : Fin n) :
    longBlock K n l (mkSL !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])) *
        longBlock K n l (mkSL !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])) ≠
      longBlock K n l (mkSL !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])) *
        longBlock K n l (mkSL !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])) := by
  intro h
  rw [← map_mul, ← map_mul] at h
  have h' := longBlock_injective l h
  have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h'
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at this
  simp [mkSL, Matrix.mul_apply, Fin.sum_univ_two] at this


theorem exists_sp_apply_eq_two_at {k l : Fin n} (hkl : k ≠ l)
    (u₁ w₁ u₂ w₂ : Fin n ⊕ Fin n → K) (h₁ : form u₁ w₁ = 1) (h₂ : form u₂ w₂ = 1)
    (o₁ : form u₁ u₂ = 0) (o₂ : form u₁ w₂ = 0) (o₃ : form w₁ u₂ = 0) (o₄ : form w₁ w₂ = 0) :
    ∃ g : StatedSp n K, mat n K g *ᵥ Pi.single (Sum.inl k) 1 = u₁ ∧
      mat n K g *ᵥ Pi.single (Sum.inr k) 1 = w₁ ∧ mat n K g *ᵥ Pi.single (Sum.inl l) 1 = u₂ ∧
      mat n K g *ᵥ Pi.single (Sum.inr l) 1 = w₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by have := k.2; have := l.2; omega⟩
  obtain ⟨g₁, a1, a2, a3, a4⟩ := exists_sp_apply_eq_two u₁ w₁ u₂ w₂ h₁ h₂ o₁ o₂ o₃ o₄
  have hkl' : l ≠ k := hkl.symm
  obtain ⟨g₂, b1, b2, b3, b4⟩ := exists_sp_apply_eq_two
    (Pi.single (Sum.inl k) (1 : K) : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K)
    (Pi.single (Sum.inr k) 1) (Pi.single (Sum.inl l) 1) (Pi.single (Sum.inr l) 1)
    (form_single_inl_inr k)
    (form_single_inl_inr l) (by rw [form_single_right]; simp)
    (by rw [form_single_right]; simp [hkl'])
    (by rw [form_single_right]; simp [hkl'])
    (by rw [form_single_right]; simp)
  refine ⟨g₁ * g₂⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff g₂ _ _).1 b1, a1]
  · rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff g₂ _ _).1 b2, a2]
  · rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff g₂ _ _).1 b3, a3]
  · rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff g₂ _ _).1 b4, a4]


end Orth

end CFSG.ClassicalInvolution.Models.SymplecticPairs
