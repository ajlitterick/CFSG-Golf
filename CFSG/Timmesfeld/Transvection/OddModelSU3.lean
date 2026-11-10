module

public import CFSG.Timmesfeld.Transvection.OddModelHeis
public import CFSG.Timmesfeld.Transvection.OddModelBlock
import CFSG.Timmesfeld.Transvection.PresSUHalf
import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3

public section

namespace CFSG.Timmesfeld.Transvection.Pres

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.LocalAnalysis.UniquenessCase
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

private theorem toStd_three_eq_self (v : Fin (3 / 2) → ℤ) : toStd 3 v = v := by
  funext a
  have ha : a.val = 0 := by have := a.isLt; omega
  rw [toStd, if_neg (show ¬ Even 3 by decide)]
  simp [ha]

theorem toStd_three_single :
    toStd 3 (Pi.single (0 : Fin (3 / 2)) 1) = wt (Sum.inl (0 : Fin (3 / 2))) := by
  rw [toStd_last_odd (k := (0 : Fin (3 / 2))) (n := 3) (by decide) (by decide)]
  exact (weight_crd (m := 3) (Sum.inl (0 : Fin (3 / 2)))).symm

private theorem toStd_three_neg_single :
    toStd 3 (-Pi.single (0 : Fin (3 / 2)) 1) = wt (Sum.inr (0 : Fin (3 / 2))) := by
  rw [toStd_three_eq_self]
  rfl


private theorem lastIdxOdd_crd_inl_zero {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) :
    lastIdxOdd k hn (crd (Sum.inl (0 : Fin (3 / 2)))) = lowIdx k := rfl

private theorem lastIdxOdd_crd_inr_zero {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) :
    lastIdxOdd k hn (crd (Sum.inr (0 : Fin (3 / 2)))) = Fin.rev (lowIdx k) := rfl

private theorem lastIdxOdd_midIdx_three {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) :
    lastIdxOdd k hn (midIdx 3 (by decide)) = midIdx n hn := rfl

theorem su3Emb_suHeis_inl {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) (u v : F) :
    su3Emb σ hn k (suHeis σ hσ (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩)
        (Sum.inl (0 : Fin (3 / 2))) u v) =
      suHeis σ hσ hn (Sum.inl k) u v := by
  by_cases h : v + σ v + σ u * u = 0
  · apply mat_injective
    rw [show su3Emb σ hn k = suEmbed σ (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn)
      from rfl]
    rw [mat_suEmbed, mat_suHeis hσ (by decide) h, mat_suHeis hσ hn h]
    rw [extendMat_heisenbergMatrix (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn)
      (crd (Sum.inl (0 : Fin (3 / 2)))) (midIdx 3 (by decide)) (rev_midIdx (by decide)) u v]
    rw [lastIdxOdd_crd_inl_zero, lastIdxOdd_midIdx_three, crd_inl]
  · rw [suHeis_of_not hσ (by decide : ¬ Even 3) h, suHeis_of_not hσ hn h, map_one]

theorem su3Emb_suHeis_inr {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) (u v : F) :
    su3Emb σ hn k (suHeis σ hσ (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩)
        (Sum.inr (0 : Fin (3 / 2))) u v) =
      suHeis σ hσ hn (Sum.inr k) u v := by
  by_cases h : v + σ v + σ u * u = 0
  · apply mat_injective
    rw [show su3Emb σ hn k = suEmbed σ (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn)
      from rfl]
    rw [mat_suEmbed, mat_suHeis hσ (by decide) h, mat_suHeis hσ hn h]
    rw [extendMat_heisenbergMatrix (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn)
      (crd (Sum.inr (0 : Fin (3 / 2)))) (midIdx 3 (by decide)) (rev_midIdx (by decide)) u v]
    rw [lastIdxOdd_crd_inr_zero, lastIdxOdd_midIdx_three, crd_inr]
  · rw [suHeis_of_not hσ (by decide : ¬ Even 3) h, suHeis_of_not hσ hn h, map_one]

theorem map_rootGroup_su3Emb {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2))
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = wt (Sum.inl k)) :
    (CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
        (Pi.single (0 : Fin (3 / 2)) 1)).map (su3Emb σ hn k) =
      CFSG.LieType.Universal.Unitary.rootGroup σ hσ n γ := by
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨u, v, h, rfl⟩ :=
      (mem_rootGroup_iff_suHeis hσ (by decide : ¬ Even 3) (a := Sum.inl (0 : Fin (3 / 2)))
        toStd_three_single A).mp hA
    exact (mem_rootGroup_iff_suHeis hσ hn (a := Sum.inl k) hγ
      (su3Emb σ hn k (suHeis σ hσ (by decide : ¬ Even 3)
        (Sum.inl (0 : Fin (3 / 2))) u v))).mpr
      ⟨u, v, h, (su3Emb_suHeis_inl hσ hn k u v).symm⟩
  · intro hx
    obtain ⟨u, v, h, rfl⟩ :=
      (mem_rootGroup_iff_suHeis hσ hn (a := Sum.inl k) hγ x).mp hx
    refine Subgroup.mem_map.mpr
      ⟨suHeis σ hσ (by decide : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u v, ?_,
        su3Emb_suHeis_inl hσ hn k u v⟩
    exact (mem_rootGroup_iff_suHeis hσ (by decide : ¬ Even 3) (a := Sum.inl (0 : Fin (3 / 2)))
      toStd_three_single _).mpr ⟨u, v, h, rfl⟩

theorem map_rootGroup_su3Emb_neg {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2))
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = wt (Sum.inr k)) :
    (CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
        (-Pi.single (0 : Fin (3 / 2)) 1)).map (su3Emb σ hn k) =
      CFSG.LieType.Universal.Unitary.rootGroup σ hσ n γ := by
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨u, v, h, rfl⟩ :=
      (mem_rootGroup_iff_suHeis hσ (by decide : ¬ Even 3) (a := Sum.inr (0 : Fin (3 / 2)))
        toStd_three_neg_single A).mp hA
    exact (mem_rootGroup_iff_suHeis hσ hn (a := Sum.inr k) hγ
      (su3Emb σ hn k (suHeis σ hσ (by decide : ¬ Even 3)
        (Sum.inr (0 : Fin (3 / 2))) u v))).mpr
      ⟨u, v, h, (su3Emb_suHeis_inr hσ hn k u v).symm⟩
  · intro hx
    obtain ⟨u, v, h, rfl⟩ :=
      (mem_rootGroup_iff_suHeis hσ hn (a := Sum.inr k) hγ x).mp hx
    refine Subgroup.mem_map.mpr
      ⟨suHeis σ hσ (by decide : ¬ Even 3) (Sum.inr (0 : Fin (3 / 2))) u v, ?_,
        su3Emb_suHeis_inr hσ hn k u v⟩
    exact (mem_rootGroup_iff_suHeis hσ (by decide : ¬ Even 3) (a := Sum.inr (0 : Fin (3 / 2)))
      toStd_three_neg_single _).mpr ⟨u, v, h, rfl⟩


end CFSG.Timmesfeld.Transvection.Pres

