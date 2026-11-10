module

public import CFSG.LocalAnalysis.StandardType.GGWeylCasePrime
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLTypeA
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLLabel
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Families

variable {X : Type*} {m : ℕ}


end Families

theorem ggCoxeterMatrix_reindex_refl {B : Type*} (M : CoxeterMatrix B) :
    M.reindex (Equiv.refl B) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

section Pairing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {m : ℕ} {hJ : ℕ → M}
  {αJ : ℕ → Module.Dual R M} {ha hb : M} {αa αb : Module.Dual R M}

theorem ggChainRoot_zero_eq {k : ℕ} (hk : k ≤ m) :
    ggChainRoot m αJ αa 0 = (∑ j ∈ Finset.range k, αJ j) + ggChainRoot m αJ αa k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih (by omega), ggChainRoot_of_lt (by omega : k < m), Finset.sum_range_succ]
    abel

theorem ggChainCoroot_zero_eq {k : ℕ} (hk : k ≤ m) :
    ggChainCoroot m hJ ha 0 = (∑ j ∈ Finset.range k, hJ j) + ggChainCoroot m hJ ha k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih (by omega), ggChainCoroot_of_lt (by omega : k < m), Finset.sum_range_succ]
    abel

theorem GGChainPairing.chainRoot_zero_apply (hP : GGChainPairing m hJ αJ ha αa) {k : ℕ}
    (hk : k < m) : ggChainRoot m αJ αa 0 (hJ k) = if k = 0 then 1 else 0 := by
  have hkk : ggChainRoot m αJ αa k (hJ k) = 1 := by
    rw [ggChainRoot_of_lt hk, LinearMap.add_apply, hP.chainRoot_succ_apply hk, hP.jj k k hk hk]
    norm_num
  have hsum : ∑ j ∈ Finset.range k, αJ j (hJ k) = if k = 0 then 0 else -1 := by
    split_ifs with hk0
    · subst hk0
      simp
    · rw [Finset.sum_eq_single (k - 1)]
      · rw [hP.jj (k - 1) k (by omega) hk]
        split_ifs <;> first | rfl | (exfalso; omega)
      · intro j hj hjk
        rw [Finset.mem_range] at hj
        rw [hP.jj j k (by omega) hk]
        split_ifs <;> first | rfl | (exfalso; omega)
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [ggChainRoot_zero_eq hk.le, LinearMap.add_apply, LinearMap.sum_apply, hsum, hkk]
  split_ifs <;> ring


end Pairing

section Generation

variable {H : Type*} [Group H]


theorem closure_union_conj (S : Set H) (a g : H) (hg : g ∈ Subgroup.closure S) :
    Subgroup.closure (S ∪ {g * a * g⁻¹}) = Subgroup.closure (S ∪ {a}) := by
  have hS : ∀ T : Set H, Subgroup.closure S ≤ Subgroup.closure (S ∪ T) := fun T =>
    Subgroup.closure_mono Set.subset_union_left
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro z (hz | rfl)
    · exact Subgroup.subset_closure (Or.inl hz)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hS _ hg) (Subgroup.subset_closure (Or.inr rfl)))
        (Subgroup.inv_mem _ (hS _ hg))
  · rw [Subgroup.closure_le]
    rintro z (hz | rfl)
    · exact Subgroup.subset_closure (Or.inl hz)
    · have h := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hS {g * z * g⁻¹} hg))
        (Subgroup.subset_closure (Or.inr rfl : g * z * g⁻¹ ∈ S ∪ {g * z * g⁻¹}))) (hS _ hg)
      rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at h

end Generation

theorem GGChainPairing.chainCoroot_self_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} (hm : 1 ≤ m) {hJ : ℕ → V}
    {αJ : ℕ → Module.Dual (ZMod p) V} {ha : V} {αa : Module.Dual (ZMod p) V}
    (hP : GGChainPairing m hJ αJ ha αa) (S : ℕ → (V ≃ₗ[ZMod p] V))
    (hS : ∀ j < m, ∀ w, S j w = w - αJ j w • hJ j) (T : V ≃ₗ[ZMod p] V)
    (hT : ∀ w, T w = w - αa w • ha) : ggChainCoroot m hJ ha m = ha := by
  have hconj := ggChainConj_apply hP S hS T hT m le_rfl
  have key : ∀ z, ggChainRoot m αJ αa m z • ggChainCoroot m hJ ha m = αa z • ha := by
    intro z
    have h1 := hconj z
    rw [ggChainProd_self, one_mul, inv_one, mul_one, hT] at h1
    exact (sub_right_injective h1).symm
  have h2 : (2 : ZMod p) • ggChainCoroot m hJ ha m = αa (ggChainCoroot m hJ ha m) • ha := by
    rw [← key, hP.chainRoot_chainCoroot m le_rfl]
  have h3 : αJ (m - 1) (ggChainCoroot m hJ ha m) = -1 := by
    have := hP.root_coroot_succ (k := m - 1) (by omega)
    rwa [show m - 1 + 1 = m by omega] at this
  have h4 : αJ (m - 1) ha = -1 := by
    rw [hP.ja (m - 1) (by omega)]
    simp [show m - 1 + 1 = m by omega]
  have h5 : αa (ggChainCoroot m hJ ha m) = 2 := by
    have := congrArg (αJ (m - 1)) h2
    rw [map_smul, map_smul, h3, h4, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  rw [h5] at h2
  exact smul_right_injective V (zmod_two_ne_zero hp2) h2


section GG

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V]

theorem mem_ggInduced_top_of_mem_ggAutomizer {H : Subgroup G} {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer H Bs) : φ ∈ ggInduced ⊤ Bs := by
  refine Subgroup.closure_induction (p := fun ψ _ => ψ ∈ ggInduced ⊤ Bs) ?_ ?_ ?_ ?_ hφ
  · rintro ψ ⟨g, -, hgN, hg⟩
    exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
  · exact one_mem_ggInduced ⊤ Bs
  · intro ψ χ _ _ h1 h2
    exact mul_mem_ggInduced h1 h2
  · intro ψ _ h
    exact inv_mem_ggInduced h


end GG


end CFSG.StandardType
