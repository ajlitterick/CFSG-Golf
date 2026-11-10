module

public import CFSG.YGroups.Defs
public import CFSG.YGroups.CosetBound

public section

namespace CFSG.YGroups

open CFSG.Certificates.CosetEnumeration

variable {p q r p' q' r' : ℕ}

theorem evalWord_yGen_map (m : ℕ → ℕ) (w : List ℕ) :
    evalWord (fun c => yGen p' q' r' (m c)) w = evalWord (yGen p' q' r') (w.map m) := by
  induction w with
  | nil => rfl
  | cons c w ih => rw [evalWord_cons, List.map_cons, evalWord_cons, ih]

theorem evalWord_congr {G : Type*} [Group G] {g g' : ℕ → G} {w : List ℕ}
    (h : ∀ c ∈ w, g c = g' c) : evalWord g w = evalWord g' w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [evalWord_cons, evalWord_cons, h c (by simp), ih (fun c' hc' => h c' (by simp [hc']))]

theorem lift_wordFG {G : Type*} [Group G] {n : ℕ} (f : Fin n → G) (w : List ℕ) :
    FreeGroup.lift f (wordFG n w) = evalWord (fun c => if h : c < n then f ⟨c, h⟩ else 1) w := by
  induction w with
  | nil => simp [wordFG, evalWord]
  | cons c w ih =>
    simp only [wordFG, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih, evalWord_cons]
    congr 1
    by_cases hc : c < n <;> simp [hc]

theorem lt_ngen_of_mem_yRels {w : List ℕ} (hw : w ∈ yRels p q r) : ∀ c ∈ w, c < ngen p q r := by
  intro c hc
  simp only [yRels, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_filter] at hw
  rcases hw with (⟨s, hs, rfl⟩ | ⟨s, hs, t, ⟨ht, -⟩, rfl⟩) | hsp
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl <;> exact hs
  · simp only [pairWord, List.mem_flatten, List.mem_replicate] at hc
    obtain ⟨l, ⟨-, rfl⟩, hcl⟩ := hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcl
    rcases hcl with rfl | rfl
    · exact hs
    · exact ht
  · split_ifs at hsp with hpqr
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsp
      subst hsp
      simp only [spiderWord, List.mem_flatten, List.mem_replicate] at hc
      obtain ⟨l, ⟨-, rfl⟩, hcl⟩ := hc
      simp only [ngen, List.mem_cons, List.mem_nil_iff, or_false] at hcl ⊢
      omega
    · simp at hsp

noncomputable def yHom (m : ℕ → ℕ) (hm : ∀ w ∈ yRels p q r, w.map m ∈ yRels p' q' r') :
    YGroup p q r →* YGroup p' q' r' :=
  PresentedGroup.toGroup (f := fun c : Fin (ngen p q r) => yGen p' q' r' (m c)) (by
    rintro x ⟨w, hw, rfl⟩
    rw [lift_wordFG, evalWord_congr (g' := fun c => yGen p' q' r' (m c)), evalWord_yGen_map]
    · exact evalWord_yGen_of_mem (hm w hw)
    · intro c hc
      simp [lt_ngen_of_mem_yRels hw c hc])

theorem yHom_yGen (m : ℕ → ℕ) (hm : ∀ w ∈ yRels p q r, w.map m ∈ yRels p' q' r') {c : ℕ}
    (hc : c < ngen p q r) : yHom m hm (yGen p q r c) = yGen p' q' r' (m c) := by
  rw [yGen_of_lt hc, yHom, PresentedGroup.toGroup.of]

theorem range_yHom (m : ℕ → ℕ) (hm : ∀ w ∈ yRels p q r, w.map m ∈ yRels p' q' r') :
    (yHom m hm).range = Subgroup.closure (yGen p' q' r' '' (m '' Set.Iio (ngen p q r))) := by
  rw [MonoidHom.range_eq_map, ← closure_yGen p q r, MonoidHom.map_closure, Set.image_image,
    Set.image_image]
  congr 1
  apply Set.image_congr
  intro c hc
  exact yHom_yGen m hm hc

theorem finite_card_le_of_index {G G' : Type*} [Group G] [Group G'] [Finite G] (φ : G →* G')
    {k : ℕ} (h : φ.range.FiniteIndex ∧ φ.range.index ≤ k) :
    Finite G' ∧ Nat.card G' ≤ k * Nat.card G := by
  have hcard := φ.range.card_mul_index
  have : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have hle : Nat.card φ.range ≤ Nat.card G :=
    Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  have hidx : φ.range.index ≠ 0 := h.1.index_ne_zero
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [← hcard]; exact Nat.mul_ne_zero hpos.ne' hidx
  · rw [← hcard, Nat.mul_comm]
    exact Nat.mul_le_mul h.2 hle


end CFSG.YGroups
