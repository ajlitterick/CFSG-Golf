module

public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.RankOneFaithful
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSASymplecticExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedGS

namespace DihedralExceptional


theorem pinnedX_commute {τ : Tag} {K : Type} [Field K] {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hαp : 0 < height α) (hβp : 0 < height β)
    (hne : α ≠ β) (hnot : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ¬ IsRoot τ (a • α + b • β)) (c d : K) :
    Commute (pinnedX τ K α c) (pinnedX τ K β d) := by
  have hbot : ⁅rootSubgroup τ K α, rootSubgroup τ K β⁆ = ⊥ := by
    refine le_bot_iff.1 ((commutator_rootSubgroup_le K hα hβ hαp hβp hne).trans ?_)
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγr, a, b, ha, hb, rfl⟩ := hγ
    exact absurd hγr (hnot a b ha hb)
  have h := Subgroup.commutator_mem_commutator (H₁ := rootSubgroup τ K α)
    (H₂ := rootSubgroup τ K β) (mem_rootSubgroup.2 ⟨c, rfl⟩) (mem_rootSubgroup.2 ⟨d, rfl⟩)
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h


structure TopRoots (τ : Tag) where
  H : ℤ
  α : Fin 3 → Fin τ.rank → ℤ
  three_lt : 3 < H
  height_le : ∀ v, IsRoot τ v → height v ≤ H
  isRoot : ∀ i, IsRoot τ (α i)
  height_eq : ∀ i : Fin 3, height (α i) = H - (i : ℕ)

namespace TopRoots

variable {τ : Tag} (R : TopRoots τ)

theorem height_pos (i : Fin 3) : 0 < height (R.α i) := by
  have := R.height_eq i
  have := R.three_lt
  have : (i : ℕ) ≤ 2 := Nat.lt_succ_iff.1 i.2
  omega

theorem injective : Function.Injective R.α := fun i j h => by
  have h' := congrArg height h
  rw [R.height_eq, R.height_eq] at h'
  exact Fin.ext (by omega)

theorem commute {K : Type} [Field K] {i j : Fin 3} (hij : i ≠ j) (c d : K) :
    Commute (pinnedX τ K (R.α i) c) (pinnedX τ K (R.α j) d) := by
  refine pinnedX_commute (R.isRoot i) (R.isRoot j) (R.height_pos i) (R.height_pos j)
    (fun h => hij (R.injective h)) (fun a b ha hb hr => ?_) c d
  have hle := R.height_le _ hr
  rw [height_nsmul_add_nsmul, R.height_eq, R.height_eq] at hle
  have hi : (i : ℕ) ≤ 2 := Nat.lt_succ_iff.1 i.2
  have hj : (j : ℕ) ≤ 2 := Nat.lt_succ_iff.1 j.2
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have hsum : ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) ≤ 3 := by omega
  have h3 := R.three_lt
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hi' : ((i : ℕ) : ℤ) ≤ 2 := by exact_mod_cast hi
  have hj' : ((j : ℕ) : ℤ) ≤ 2 := by exact_mod_cast hj
  nlinarith [mul_nonneg (sub_nonneg.2 ha') (by linarith : (0 : ℤ) ≤ R.H - (i : ℕ)),
    mul_nonneg (sub_nonneg.2 hb') (by linarith : (0 : ℤ) ≤ R.H - (j : ℕ))]


end TopRoots


end DihedralExceptional

open DihedralExceptional


end CFSG.ComponentClassification.UnbalancingLocal
