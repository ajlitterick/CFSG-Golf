module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XModelCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XAutDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def IsBase01 (K : Subgroup (Equiv.Perm (Fin 1408))) : Prop :=
  ∀ g ∈ K, idx 1408 g 0 = 0 → idx 1408 g 1 = 1 → g = 1

theorem ap_ap_rep {x y : Table} {g h : Equiv.Perm (Fin 1408)} (hx : Rep 1408 x g)
    (hy : Rep 1408 y h) {i : ℕ} (hi : i < 1408) : ap x (ap y i) = idx 1408 (g * h) i := by
  rw [hy i hi, hx _ (idx_lt h hi), idx_mul]

theorem eq_of_base01 {K : Subgroup (Equiv.Perm (Fin 1408))} (hK : IsBase01 K)
    {a b : Equiv.Perm (Fin 1408)} (ha : a ∈ K) (hb : b ∈ K) (h0 : idx 1408 a 0 = idx 1408 b 0)
    (h1 : idx 1408 a 1 = idx 1408 b 1) : a = b := by
  have key : a⁻¹ * b = 1 := by
    refine hK _ (K.mul_mem (K.inv_mem ha) hb) ?_ ?_
    · rw [idx_mul, ← h0, idx_inv_idx]
    · rw [idx_mul, ← h1, idx_inv_idx]
  exact inv_mul_eq_one.mp key


theorem commB_iff {K : Subgroup (Equiv.Perm (Fin 1408))} (hK : IsBase01 K) {x y : Table}
    {g h : Equiv.Perm (Fin 1408)} (hx : Rep 1408 x g) (hy : Rep 1408 y h) (hg : g ∈ K)
    (hh : h ∈ K) : commB x y = true ↔ g * h = h * g := by
  have e : ∀ i < 1408, ap x (ap y i) = idx 1408 (g * h) i ∧ ap y (ap x i) = idx 1408 (h * g) i :=
    fun i hi => ⟨ap_ap_rep hx hy hi, ap_ap_rep hy hx hi⟩
  rw [commB, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, (e 0 (by norm_num)).1,
    (e 0 (by norm_num)).2, (e 1 (by norm_num)).1, (e 1 (by norm_num)).2]
  constructor
  · rintro ⟨h0, h1⟩
    exact eq_of_base01 hK (K.mul_mem hg hh) (K.mul_mem hh hg) h0 h1
  · intro hgh
    rw [hgh]
    exact ⟨rfl, rfl⟩


end CFSG.EvenSporadicStandard.HNRecog.Section4.XModel
