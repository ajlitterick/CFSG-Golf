module

public import CFSG.ClassicalInvolution.Q3.AE.Bar

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem zQ_comm_kList : ∀ a ∈ kList, zQ * a = a * zQ := by decide +kernel

theorem zQ_comm_kStarList : ∀ a ∈ kStarList, zQ * a = a * zQ := by decide +kernel

theorem kList_not_comm : ∃ a ∈ kList, ∃ b ∈ kList, a * b ≠ b * a := by decide +kernel

theorem kStarList_not_comm : ∃ a ∈ kStarList, ∃ b ∈ kStarList, a * b ≠ b * a := by
  decide +kernel

theorem zBar_mul_self (α : Finset (Fin n)) (h : α.card = 4) : zBar α h * zBar α h = 1 := by
  rw [zBar, ← map_mul, mul_eq_one_iff_eq_inv.mpr (zOf_inv _).symm, map_one]

theorem zOf_comm_memAt (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∀ a ∈ memAt α h b, zOf (emb α h) * a = a * zOf (emb α h) := by
  cases b
  · rintro _ ⟨a, ha, rfl⟩
    unfold zOf
    rw [← map_mul, ← map_mul, zQ_comm_kStarList a ha]
  · rintro _ ⟨a, ha, rfl⟩
    unfold zOf
    rw [← map_mul, ← map_mul, zQ_comm_kList a ha]

theorem zBar_comm_memBar (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∀ x ∈ memBar α h b, zBar α h * x = x * zBar α h := by
  rintro _ ⟨a, ha, rfl⟩
  rw [zBar, ← map_mul, ← map_mul, zOf_comm_memAt α h b a ha]

theorem exists_not_comm_memAt (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∃ a ∈ memAt α h b, ∃ a' ∈ memAt α h b, a * a' ≠ a' * a := by
  obtain ⟨a, ha, a', ha', hne⟩ : ∃ a ∈ (bif b then kQ else kQStar : Subgroup (Wr 4)),
      ∃ a' ∈ (bif b then kQ else kQStar : Subgroup (Wr 4)), a * a' ≠ a' * a := by
    cases b
    · exact kStarList_not_comm
    · exact kList_not_comm
  refine ⟨embed (emb α h) a, ?_, embed (emb α h) a', ?_, fun he => hne ?_⟩
  · cases b
    · exact ⟨a, ha, rfl⟩
    · exact ⟨a, ha, rfl⟩
  · cases b
    · exact ⟨a', ha', rfl⟩
    · exact ⟨a', ha', rfl⟩
  · rw [← map_mul, ← map_mul] at he
    exact embed_injective _ he

theorem exists_not_comm_memBar (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∃ x ∈ memBar α h b, ∃ x' ∈ memBar α h b, x * x' ≠ x' * x := by
  obtain ⟨a, ha, a', ha', hne⟩ := exists_not_comm_memAt α h b
  refine ⟨mkQ n a, ⟨a, ha, rfl⟩, mkQ n a', ⟨a', ha', rfl⟩, fun he => hne ?_⟩
  exact comm_of_mkQ_comm_of_supportedOn hn (supportedOn_of_mem_memAt ha)
    (supportedOn_of_mem_memAt ha') he


end CFSG.ClassicalInvolution.Q3.AE
