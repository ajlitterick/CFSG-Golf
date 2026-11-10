module

public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

variable {n : ℕ}

theorem rep_evalW (hn : n < 2 ^ 32) {ι : Type} {G : Type*} [Group G] [MulAction G (Fin n)]
    {g gi : ι → Table} {f : ι → G} (hg : ∀ i, Rep n (g i) (f i))
    (hgi : ∀ i, Rep n (gi i) (f i)⁻¹) (w : List (ι × Bool)) :
    Rep n (evalW n g gi w) (FreeGroup.lift f (FreeGroup.mk w)) := by
  have key : ∀ (w : List (ι × Bool)) (acc : Table) (a : G), Rep n acc a →
      Rep n (w.foldl (fun acc l => compT n acc (if l.2 then g l.1 else gi l.1)) acc)
        (a * (w.map fun x => cond x.2 (f x.1) (f x.1)⁻¹).prod) := by
    intro w
    induction w with
    | nil => intro acc a h; simpa using h
    | cons l w ih =>
      intro acc a h
      rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
      refine ih _ _ (Rep.compT h ?_)
      obtain ⟨i, b⟩ := l
      cases b <;> simp [hg, hgi]
  have := key w (idT n) 1 (Rep.idT hn)
  rw [FreeGroup.lift_mk]
  simpa [evalW] using this

theorem rep_wordTbl' (hn : n < 2 ^ 32) {gs : List Table} (hg : ∀ g ∈ gs, permOK n g = true)
    (w : List ℕ) (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ gs.length) :
    Rep n (wordTbl n gs w) (w.map fun l => tp n (gs.getD (l - 1) (idT n))).prod := by
  have key : ∀ (w : List ℕ), (∀ l ∈ w, 1 ≤ l ∧ l ≤ gs.length) → ∀ (acc : Table)
      (a : Equiv.Perm (Fin n)), Rep n acc a →
      Rep n (w.foldl (fun acc l => compT n acc (gs.getD (l - 1) (idT n))) acc)
        (a * (w.map fun l => tp n (gs.getD (l - 1) (idT n))).prod) := by
    intro w
    induction w with
    | nil => intro _ acc a h; simpa using h
    | cons l w ih =>
      intro hw acc a h
      rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
      obtain ⟨hl1, hl2⟩ := hw l List.mem_cons_self
      have hmem : gs.getD (l - 1) (idT n) ∈ gs := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem l hl')) _ _
        (Rep.compT h (rep_tp (hg _ hmem)))
  have := key w hw (idT n) 1 (Rep.idT hn)
  simpa [wordTbl] using this

@[expose] def wordVal {M : Type*} [Group M] (gs : List M) (w : List ℕ) : M :=
  (w.map fun l => gs.getD (l - 1) 1).prod

theorem map_wordVal {M N : Type*} [Group M] [Group N] (f : M →* N) (gs : List M) (w : List ℕ) :
    f (wordVal gs w) = wordVal (gs.map f) w := by
  unfold wordVal
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply]
  by_cases h : l - 1 < gs.length
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using h)]
    simp

theorem rep_wordTbl'' (hn : n < 2 ^ 32) {gs : List Table} (hg : ∀ g ∈ gs, permOK n g = true)
    (w : List ℕ) (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ gs.length) :
    Rep n (wordTbl n gs w) (wordVal (gs.map (tp n)) w) := by
  have h := rep_wordTbl' hn hg w hw
  convert h using 2
  unfold wordVal
  congr 1
  apply List.map_congr_left
  intro l hl
  obtain ⟨hl1, hl2⟩ := hw l hl
  rw [List.getD_eq_getElem _ _ (by simpa using (show l - 1 < gs.length by omega)),
    List.getD_eq_getElem _ _ (by omega)]
  simp


theorem mem_genOf_of_memT {cap m : ℕ} {gs : List Table} (hn : n < 2 ^ 32)
    (hg : ∀ g ∈ gs, permOK n g = true) (h : enumOK n cap m gs = true) {x : Table}
    {g : Equiv.Perm (Fin n)} (hx : Rep n x g)
    (hm : memT n (mulClosureH n gs.toArray cap).1 x = true) : g ∈ genOf n gs := by
  obtain ⟨-, hrep, -, -⟩ := enumOK_spec hn hg h
  obtain ⟨k, hk, hgk⟩ := memT_spec (fun k hk => (hrep k hk).1) hx hm
  rw [hgk]
  exact (hrep k hk).2


end CFSG.EvenSporadicStandard.TwoHS
