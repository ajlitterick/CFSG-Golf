module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

@[expose] def walkRoot (L : ℕ) (tab fwd : Array ℕ) (fuel : ℕ) : ℕ → List ℕ → Option ℕ
  | c, [] => some (find fwd fuel c)
  | c, y :: w =>
    let d := tab.getD (find fwd fuel c * L + y) 0
    if d = 0 then none else walkRoot L tab fwd fuel d w

section Walk

variable {G : Type*} [Group G] {L : ℕ} {gen : ℕ → G} {H : Subgroup G}


end Walk

variable {m : ℕ}

@[expose] def relCheck (ws : List (List (Fin m × Bool))) (cap : ℕ)
    (us : List (List (Fin m × Bool))) : Bool :=
  let P := presParams ws []
  let st := enumerateHLT P cap
  (codes us).all fun w => walkRoot P.L st.tab st.fwd st.next 1 w == some 1


theorem lift_of_mk {ws : List (List (Fin m × Bool))} (w : List (Fin m × Bool)) :
    FreeGroup.lift (PresentedGroup.of : Fin m → PG m ws) (FreeGroup.mk w) =
      PresentedGroup.mk _ (FreeGroup.mk w) := by
  have : FreeGroup.lift (PresentedGroup.of : Fin m → PG m ws) =
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  rw [this]

noncomputable def mulEquivAppend (ws us : List (List (Fin m × Bool)))
    (h : ∀ u ∈ us, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u) = 1) : PG m (ws ++ us) ≃* PG m ws :=
  have hf : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ (ws ++ us).map FreeGroup.mk},
      FreeGroup.lift (PresentedGroup.of : Fin m → PG m ws) r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_append] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [lift_of_mk]
    rcases hw with hw | hw
    · exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)
    · exact h w hw
  have hg : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk},
      FreeGroup.lift (PresentedGroup.of : Fin m → PG m (ws ++ us)) r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [lift_of_mk]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (List.mem_append_left _ hw))
  MonoidHom.toMulEquiv (PresentedGroup.toGroup hf) (PresentedGroup.toGroup hg)
    (PresentedGroup.ext fun x => by simp)
    (PresentedGroup.ext fun x => by simp)

theorem card_le_of_append (ws us : List (List (Fin m × Bool)))
    (h : ∀ u ∈ us, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u) = 1) {n : ℕ}
    (hn : Finite (PG m (ws ++ us)) ∧ Nat.card (PG m (ws ++ us)) ≤ n) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n := by
  have e := mulEquivAppend ws us h
  obtain ⟨hfin, hle⟩ := hn
  exact ⟨Finite.of_equiv _ e.toEquiv, (Nat.card_congr e.toEquiv).symm ▸ hle⟩

end CFSG.CosetTable
