module

public import CFSG.ClassicalInvolution.SmallCases.SmallWeylRootFamily

public section

namespace CFSG.ClassicalInvolution.SmallWeyl


structure IsAutC (g : ℕ × ℕ → ℕ × ℕ) : Prop where
  valid : ∀ a ∈ allC 4, validC 4 (g a) = true
  invol : ∀ a ∈ allC 4, g (g a) = a
  pair : ∀ a ∈ allC 4, ∀ b ∈ allC 4, pairC (g a).2 (g b).1 = pairC a.2 b.1
  add : ∀ a ∈ allC 4, ∀ b ∈ allC 4, adjC a b = true → g (addC a b) = addC (g a) (g b)


namespace IsAutC

variable {g : ℕ × ℕ → ℕ × ℕ} (hg : IsAutC g)
include hg

theorem adjC_eq {a b : ℕ × ℕ} (ha : validC 4 a = true) (hb : validC 4 b = true) :
    adjC (g a) (g b) = adjC a b := by
  have ha' := mem_allC.mpr ha
  have hb' := mem_allC.mpr hb
  simp only [adjC, hg.pair a ha' b hb', hg.pair b hb' a ha']

theorem injOn {R : Finset (ℕ × ℕ)} (hR : ∀ x ∈ R, validC 4 x = true) : Set.InjOn g R := by
  intro a ha b hb hab
  have h1 := hg.invol a (mem_allC.mpr (hR a ha))
  have h2 := hg.invol b (mem_allC.mpr (hR b hb))
  rw [← h1, ← h2, hab]

theorem codedSet_image {R : Finset (ℕ × ℕ)} (hR : CodedSet 4 R) : CodedSet 4 (R.image g) where
  valid := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hg.valid a (mem_allC.mpr (hR.valid a ha))
  closed := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    rw [hg.adjC_eq (hR.valid a ha) (hR.valid b hb)] at hxy
    rw [← hg.add a (mem_allC.mpr (hR.valid a ha)) b (mem_allC.mpr (hR.valid b hb)) hxy]
    exact Finset.mem_image_of_mem _ (hR.closed a ha b hb hxy)
  sym := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    rw [hg.pair a (mem_allC.mpr (hR.valid a ha)) b (mem_allC.mpr (hR.valid b hb)),
      hg.pair b (mem_allC.mpr (hR.valid b hb)) a (mem_allC.mpr (hR.valid a ha))]
    exact hR.sym a ha b hb
  conn := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    refine (hR.conn a ha b hb).lift g fun u v huv => ?_
    refine ⟨Finset.mem_image_of_mem _ huv.1, Finset.mem_image_of_mem _ huv.2.1, ?_⟩
    rw [hg.adjC_eq (hR.valid u huv.1) (hR.valid v huv.2.1)]
    exact huv.2.2

theorem goodSet_of_image {R : Finset (ℕ × ℕ)} (hR : CodedSet 4 R) {tab : List (ℕ × ℕ)}
    (h : GoodSet tab (R.image g)) : GoodSet tab R := by
  obtain ⟨e, he, hcard, hval⟩ := h
  have hinj := hg.injOn hR.valid
  refine ⟨e, he, ?_, fun p hp => ?_⟩
  · rw [← hcard, Finset.card_image_of_injOn hinj]
  · have hfilt : (R.image g).filter (fun q => q ≠ g p ∧ adjC (g p) q = false) =
        (R.filter fun q => q ≠ p ∧ adjC p q = false).image g := by
      ext q'
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨q, hq, rfl⟩, hne, hadj⟩
        refine ⟨q, ⟨hq, fun h => hne (h ▸ rfl), ?_⟩, rfl⟩
        rwa [hg.adjC_eq (hR.valid p hp) (hR.valid q hq)] at hadj
      · rintro ⟨q, ⟨hq, hne, hadj⟩, rfl⟩
        refine ⟨⟨q, hq, rfl⟩, fun h => hne (hinj hq hp h), ?_⟩
        rwa [hg.adjC_eq (hR.valid p hp) (hR.valid q hq)]
    rw [← Finset.card_image_of_injOn (f := g)
      (hinj.mono fun x hx => (Finset.mem_filter.mp hx).1), ← hfilt]
    exact hval _ (Finset.mem_image_of_mem _ hp)

end IsAutC

inductive Red (gens : List (ℕ × ℕ → ℕ × ℕ)) (a₀ b₀ : ℕ × ℕ) : ℕ × ℕ → ℕ × ℕ → Prop
  | base : Red gens a₀ b₀ a₀ b₀
  | step (g : ℕ × ℕ → ℕ × ℕ) (hg : g ∈ gens) {a b : ℕ × ℕ} :
      Red gens a₀ b₀ (g a) (g b) → Red gens a₀ b₀ a b

theorem Red.normalize {gens : List (ℕ × ℕ → ℕ × ℕ)} (hgens : ∀ g ∈ gens, IsAutC g)
    {a₀ b₀ a b : ℕ × ℕ} (h : Red gens a₀ b₀ a b) :
    ∀ R : Finset (ℕ × ℕ), CodedSet 4 R → a ∈ R → b ∈ R →
      ∃ R' : Finset (ℕ × ℕ), CodedSet 4 R' ∧ a₀ ∈ R' ∧ b₀ ∈ R' ∧
        ∀ tab, GoodSet tab R' → GoodSet tab R := by
  induction h with
  | base => exact fun R hR ha hb => ⟨R, hR, ha, hb, fun _ h => h⟩
  | @step g hg a b _ ih =>
    intro R hR ha hb
    obtain ⟨R', hR', h1, h2, h3⟩ := ih (R.image g) ((hgens g hg).codedSet_image hR)
      (Finset.mem_image_of_mem _ ha) (Finset.mem_image_of_mem _ hb)
    exact ⟨R', hR', h1, h2, fun tab h => (hgens g hg).goodSet_of_image hR (h3 tab h)⟩

theorem descent {X : Type*} {Q P : X → Prop} {gens : List (X → X)} {depth : X → ℕ} {x₀ : X}
    (hx₀ : P x₀) (hdesc : ∀ x, Q x → x ≠ x₀ → ∃ g ∈ gens, Q (g x) ∧ depth (g x) < depth x)
    (hstep : ∀ g ∈ gens, ∀ x, Q x → P (g x) → P x) : ∀ x, Q x → P x := by
  intro x
  induction h : depth x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro hQ
    by_cases hx : x = x₀
    · rw [hx]
      exact hx₀
    · obtain ⟨g, hg, hQg, hlt⟩ := hdesc x hQ hx
      exact hstep g hg x hQ (ih (depth (g x)) (h ▸ hlt) (g x) rfl hQg)


section Dimension


end Dimension

end CFSG.ClassicalInvolution.SmallWeyl

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.SmallWeyl


end CFSG.ClassicalInvolution.Balance
