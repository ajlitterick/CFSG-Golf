module

public import CFSG.Quasithin.Vol2.Ch3E213MP6EB
public import CFSG.Quasithin.Vol2.E2StatementsAS
import all CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6Enc

public section

namespace CFSG.Quasithin.RonanE27

open Equiv CFSG.Quasithin CFSG.Quasithin.Ch3E213M.P6E CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Borel252.A6

@[expose] def s06L : List R6 := d0L ++ d0L.map (· * R6.enc zB)

theorem mem_S06_iff {x : P6} : x ∈ S06 ↔ R6.enc x ∈ s06L := by
  constructor
  · exact enc_mem_s06L
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact Or.inl ((mem_D0 x).2 h)
    · obtain ⟨r, hr, hrx⟩ := List.mem_map.1 h
      obtain ⟨y, hy, rfl⟩ := sound_D0 r hr
      refine Or.inr ?_
      have h1 : x = y * zB := R6.enc_inj (by rw [R6.enc_mul, hrx.symm])
      rw [h1, mul_assoc, zB_mul_self, mul_one]
      exact hy


theorem chk_comm : ∀ s : P6, R6.enc s ∈ s06L → zA * s = s * zA ∧ zB * s = s * zB := by
  decide +kernel

theorem Z6_comm {z s : P6} (hz : z ∈ Z6) (hs : s ∈ S06) : z * s = s * z := by
  obtain ⟨hA, hB⟩ := chk_comm s (mem_S06_iff.1 hs)
  rcases hz with hz | hz
  · rcases mem_inf_VA_VB hz with rfl | rfl
    · simp
    · exact hA
  · rcases mem_inf_VA_VB hz with h | h
    · have : z = zB := by
        calc z = z * zB * zB := by rw [mul_assoc, zB_mul_self, mul_one]
          _ = zB := by rw [h, one_mul]
      rw [this]; exact hB
    · have : z = zA * zB := by
        calc z = z * zB * zB := by rw [mul_assoc, zB_mul_self, mul_one]
          _ = zA * zB := by rw [h]
      rw [this, mul_assoc, hB, ← mul_assoc, hA, mul_assoc]


end CFSG.Quasithin.RonanE27
