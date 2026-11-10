module

public import CFSG.Certificates.CosetTableRelations

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

@[expose] def substWord {k : ℕ} (hs : List (List (Fin m × Bool))) (r : List (Fin k × Bool)) :
    List (Fin m × Bool) :=
  r.flatMap fun l => if l.2 then hs.getD l.1 [] else FreeGroup.invRev (hs.getD l.1 [])

theorem lift_substWord {k : ℕ} {rels : Set (FreeGroup (Fin m))} (hs : List (List (Fin m × Bool)))
    (r : List (Fin k × Bool)) :
    FreeGroup.lift (fun i : Fin k => PresentedGroup.mk rels (FreeGroup.mk (hs.getD i [])))
      (FreeGroup.mk r) = PresentedGroup.mk rels (FreeGroup.mk (substWord hs r)) := by
  induction r with
  | nil => simp [substWord]; rfl
  | cons l r ih =>
    obtain ⟨i, b⟩ := l
    rw [show FreeGroup.mk ((i, b) :: r) = FreeGroup.mk [(i, b)] * FreeGroup.mk r from
      by rw [FreeGroup.mul_mk]; rfl, map_mul, ih]
    simp only [substWord, List.flatMap_cons]
    rw [← FreeGroup.mul_mk, map_mul]
    congr 1
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← FreeGroup.inv_mk, map_inv, show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl,
        map_inv, FreeGroup.lift_apply_of]
    · simp only [↓reduceIte]
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]


end CFSG.CosetTable
