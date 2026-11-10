module

public import Certificates.Data.CFSGNative.MonsterAxis.Cover
public import CFSG.Monster.VisCert.FrameSpec
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Monster.AxisCount.Native.Cover

theorem allFrom_iff (p : ℕ → Bool) :
    ∀ lo len, allFrom p lo len = true ↔ ∀ k < len, p (lo + k) = true
  | lo, 0 => by simp [allFrom]
  | lo, len + 1 => by
    rw [allFrom]
    by_cases h : p lo = true
    · rw [ite_eq_left h, allFrom_iff p (lo + 1) len]
      constructor
      · intro h' k hk
        rcases k with _ | k
        · simpa using h
        · have := h' k (by omega)
          rwa [show lo + 1 + k = lo + (k + 1) by omega] at this
      · intro h' k hk
        have := h' (k + 1) (by omega)
        rwa [show lo + (k + 1) = lo + 1 + k by omega] at this
    · rw [ite_eq_right h]
      simp only [Bool.false_eq_true, false_iff, not_forall]
      exact ⟨0, by omega, by simpa using h⟩

theorem countGo_eq (p : ℕ → Bool) :
    ∀ n acc, countGo p n acc = acc + ((Finset.range n).filter fun i => p i = true).card
  | 0, acc => by simp [countGo]
  | n + 1, acc => by
    rw [countGo, countGo_eq p n, Finset.range_add_one, Finset.filter_insert]
    by_cases h : p n = true
    · rw [ite_eq_left h, ite_eq_left h, Finset.card_insert_of_notMem (by simp)]
      ring
    · rw [ite_eq_right h, ite_eq_right h]

theorem countBelow_eq (p : ℕ → Bool) (n : ℕ) :
    countBelow p n = ((Finset.range n).filter fun i => p i = true).card := by
  rw [countBelow, countGo_eq, zero_add]


theorem actGo_lt (rows : Array ℕ) (v : ℕ) (hr : ∀ i < 24, rows[i]! < 2 ^ 24) :
    ∀ n acc, n ≤ 24 → acc < 2 ^ 24 → actGo rows v n acc < 2 ^ 24
  | 0, acc, _, h => h
  | n + 1, acc, hn, h => by
    rw [actGo]
    refine actGo_lt rows v hr n _ (by omega) ?_
    by_cases hb : v.testBit n = true
    · rw [ite_eq_left hb]
      exact Nat.xor_lt_two_pow h (hr n (by omega))
    · rw [ite_eq_right hb]
      exact h

@[expose] def foundSet (T : CoverTables) : Finset ℕ :=
  (Finset.range (2 ^ 24)).filter fun v => rd8 T.lab v ≠ 0

@[expose] def labelSet (T : CoverTables) (o : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ 24)).filter fun v => rd8 T.lab v = o

structure CoverFacts (T : CoverTables) (rows : Array (Array ℕ)) (seeds sizes : Array ℕ) :
    Prop where
  rows_size : rows.size = 2
  rows_lt : ∀ g < 2, ∀ i < 24, (rows[g]!)[i]! < 2 ^ 24
  sizes_size : seeds.size = sizes.size
  point : ∀ v < 2 ^ 24, cvOK T rows seeds v = true
  card_found : (foundSet T).card = deltaCount
  card_label : ∀ r < seeds.size, (labelSet T (r + 1)).card = sizes[r]!
  seed : ∀ r < seeds.size, seeds[r]! < 2 ^ 24 ∧ rd8 T.lab seeds[r]! = r + 1


theorem cvOK_spec {T : CoverTables} {rows : Array (Array ℕ)} {seeds : Array ℕ} {v : ℕ}
    (h : cvOK T rows seeds v = true) (hl : rd8 T.lab v ≠ 0) :
    rd8 T.lab v ≤ seeds.size ∧
    (rd8 T.lev v = 1 → v = seeds[rd8 T.lab v - 1]!) ∧
    (rd8 T.lev v ≠ 1 → rd8 T.lev v ≠ 0 ∧ rd32 T.par v < 2 ^ 24 ∧ rd8 T.gen v < 2 ∧
      rd8 T.lab (rd32 T.par v) = rd8 T.lab v ∧ rd8 T.lev (rd32 T.par v) + 1 = rd8 T.lev v ∧
      cvImg rows (rd8 T.gen v) (rd32 T.par v) = v) ∧
    (∀ j < 2, rd8 T.lab (cvImg rows j v) = rd8 T.lab v) := by
  unfold cvOK at h
  rw [ite_eq_right (by simpa using hl)] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨ho, hd⟩, hcl⟩ := h
  refine ⟨ho, fun h1 => ?_, fun h1 => ?_, fun j hj => ?_⟩
  · rw [ite_eq_left (by simpa using h1)] at hd
    simpa using hd
  · rw [ite_eq_right (by simpa using h1)] at hd
    simpa [Bool.and_eq_true, and_assoc] using hd
  · have := (allFrom_iff _ 0 2).1 hcl j hj
    rw [zero_add] at this
    simpa using this

section Orbits

variable {G X : Type*} [Group G] [MulAction G X] {T : CoverTables} {rows : Array (Array ℕ)}
  {seeds sizes : Array ℕ} {dec : ℕ → X} {gens : ℕ → G}

namespace CoverFacts

theorem cvImg_lt (hF : CoverFacts T rows seeds sizes) {g : ℕ} (hg : g < 2) (v : ℕ) :
    cvImg rows g v < 2 ^ 24 :=
  actGo_lt _ v (hF.rows_lt g hg) 24 0 le_rfl (by norm_num)

theorem mem_orbit (hF : CoverFacts T rows seeds sizes)
    (hk : ∀ g < 2, ∀ p, dec (cvImg rows g p) = gens g • dec p) :
    ∀ v < 2 ^ 24, rd8 T.lab v ≠ 0 →
      dec v ∈ MulAction.orbit (Subgroup.closure (gens '' Set.Iio 2))
        (dec seeds[rd8 T.lab v - 1]!) := by
  intro v hv hl
  induction hlev : rd8 T.lev v using Nat.strong_induction_on generalizing v with
  | _ l ih =>
    obtain ⟨-, h1, hpar, -⟩ := cvOK_spec (hF.point v hv) hl
    by_cases hl1 : rd8 T.lev v = 1
    · rw [← h1 hl1]
      exact MulAction.mem_orbit_self _
    · obtain ⟨hl0, hp, hg, hlab, hlev', himg⟩ := hpar hl1
      have hpl : rd8 T.lab (rd32 T.par v) ≠ 0 := by rw [hlab]; exact hl
      have ihp := ih _ (by omega) _ hp hpl rfl
      rw [hlab] at ihp
      have e : dec v = gens (rd8 T.gen v) • dec (rd32 T.par v) := by rw [← hk _ hg, himg]
      rw [e]
      exact CFSG.Monster.VisCert.smul_mem_orbit_closure (S := gens '' Set.Iio 2)
        (Set.mem_image_of_mem gens (Set.mem_Iio.2 hg)) ihp


theorem cvImg_mem_labelSet (hF : CoverFacts T rows seeds sizes) {o v : ℕ} (ho : o ≠ 0)
    (hv : v ∈ labelSet T o) {j : ℕ} (hj : j < 2) : cvImg rows j v ∈ labelSet T o := by
  simp only [labelSet, Finset.mem_filter, Finset.mem_range] at hv ⊢
  obtain ⟨hv24, hlab⟩ := hv
  have hl : rd8 T.lab v ≠ 0 := by rw [hlab]; exact ho
  obtain ⟨-, -, -, hcl⟩ := cvOK_spec (hF.point v hv24) hl
  exact ⟨hF.cvImg_lt hj v, (hcl j hj).trans hlab⟩

theorem seed_mem_labelSet (hF : CoverFacts T rows seeds sizes) {r : ℕ} (hr : r < seeds.size) :
    seeds[r]! ∈ labelSet T (r + 1) := by
  obtain ⟨h1, h2⟩ := hF.seed r hr
  simp only [labelSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨h1, h2⟩


theorem injOn_dec (hdec : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b)
    (s : Finset ℕ) (hs : s ⊆ Finset.range (2 ^ 24)) : Set.InjOn dec (s : Set ℕ) :=
  fun a ha b hb hab => hdec a b (Finset.mem_range.1 (hs ha)) (Finset.mem_range.1 (hs hb)) hab

theorem orbit_eq (hF : CoverFacts T rows seeds sizes)
    (hk : ∀ g < 2, ∀ p, dec (cvImg rows g p) = gens g • dec p) {r : ℕ} (hr : r < seeds.size) :
    MulAction.orbit (Subgroup.closure (gens '' Set.Iio 2)) (dec seeds[r]!) =
      dec '' (labelSet T (r + 1) : Set ℕ) := by
  refine Set.Subset.antisymm (CFSG.Monster.VisCert.orbit_closure_subset
    ((labelSet T (r + 1)).finite_toSet.image dec) ?_
    ⟨_, hF.seed_mem_labelSet hr, rfl⟩) ?_
  · rintro _ ⟨j, hj, rfl⟩ _ ⟨v, hv, rfl⟩
    have hj' : j < 2 := Set.mem_Iio.1 hj
    exact ⟨cvImg rows j v, hF.cvImg_mem_labelSet (Nat.succ_ne_zero r) hv hj', hk j hj' v⟩
  · rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ labelSet T (r + 1) := hv
    simp only [labelSet, Finset.mem_filter, Finset.mem_range] at hv'
    obtain ⟨hv24, ho⟩ := hv'
    have := hF.mem_orbit hk v hv24 (by rw [ho]; exact Nat.succ_ne_zero r)
    rwa [ho, Nat.add_sub_cancel] at this

theorem ncard_orbit (hF : CoverFacts T rows seeds sizes)
    (hk : ∀ g < 2, ∀ p, dec (cvImg rows g p) = gens g • dec p)
    (hdec : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b) {r : ℕ}
    (hr : r < seeds.size) :
    (MulAction.orbit (Subgroup.closure (gens '' Set.Iio 2)) (dec seeds[r]!)).ncard =
      sizes[r]! := by
  rw [hF.orbit_eq hk hr,
    (injOn_dec hdec (labelSet T (r + 1)) (Finset.filter_subset _ _)).ncard_image,
    Set.ncard_coe_finset, hF.card_label r hr]


theorem disjoint_orbit (hF : CoverFacts T rows seeds sizes)
    (hk : ∀ g < 2, ∀ p, dec (cvImg rows g p) = gens g • dec p)
    (hdec : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b) {r r' : ℕ}
    (hr : r < seeds.size) (hr' : r' < seeds.size) (hne : r ≠ r') :
    Disjoint (MulAction.orbit (Subgroup.closure (gens '' Set.Iio 2)) (dec seeds[r]!))
      (MulAction.orbit (Subgroup.closure (gens '' Set.Iio 2)) (dec seeds[r']!)) := by
  rw [hF.orbit_eq hk hr, hF.orbit_eq hk hr', Set.disjoint_left]
  rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hvw⟩
  have hv' : v ∈ labelSet T (r + 1) := hv
  have hw' : w ∈ labelSet T (r' + 1) := hw
  simp only [labelSet, Finset.mem_filter, Finset.mem_range] at hv' hw'
  have := hdec w v hw'.1 hv'.1 hvw
  subst this
  exact hne (by omega)


end CoverFacts

end Orbits


end CFSG.Monster.AxisCount.Native.Cover
