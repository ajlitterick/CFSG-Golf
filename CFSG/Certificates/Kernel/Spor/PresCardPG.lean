module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.Sporadic.Schreier.TitsBasic
public import CFSG.Certificates.NativeValidSchreier

public section

namespace CFSG.KS.PresPG

open CFSG.CosetTable CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem card_closure_le_PG {m : ℕ} {ws : List (List (Fin m × Bool))} [Finite (PG m ws)]
    {G : Type*} [Group G] (x : Fin m → G) (h : ∀ w ∈ ws, FreeGroup.lift x (FreeGroup.mk w) = 1) :
    Nat.card (Subgroup.closure (Set.range x)) ≤ Nat.card (PG m ws) := by
  have hr : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}, FreeGroup.lift x r = 1 := by
    rintro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact h w hw
  let φ : PG m ws →* G := PresentedGroup.toGroup hr
  have hle : Subgroup.closure (Set.range x) ≤ φ.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of hr⟩
  have hs := φ.rangeRestrict_surjective
  have : Finite φ.range := Finite.of_surjective _ hs
  exact (Subgroup.card_le_of_le hle).trans (Nat.card_le_card_of_surjective _ hs)

theorem wordIn_mem_closure {G : Type*} [Group G] (k : ℕ) (gs : ℕ → G) (w : List ℤ) :
    CFSG.Sporadic.Schreier.Tits.wordIn k gs w ∈
      Subgroup.closure (Set.range fun h : Fin k => gs h.val) := by
  unfold CFSG.Sporadic.Schreier.Tits.wordIn Quiver.SchreierGraph.evalWord
  rw [← FreeGroup.range_lift_eq_closure]
  exact ⟨_, rfl⟩


end CFSG.KS.PresPG

end
