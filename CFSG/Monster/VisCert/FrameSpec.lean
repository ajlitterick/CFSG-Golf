module

public import Certificates.Data.CFSGNative.MonsterVis.Frame
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Monster.VisCert

open Native

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

theorem parAll_spec {n chunks : ℕ} {p : ℕ → Bool} (hc : 0 < chunks)
    (h : parAll n chunks p = true) : ∀ i < n, p i = true := by
  intro i hi
  unfold parAll at h
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply] at h
  set sz := n / chunks + 1 with hsz
  have hsz0 : 0 < sz := Nat.succ_pos _
  have hj : i / sz < chunks := by
    rw [Nat.div_lt_iff_lt_mul hsz0]
    have h1 := Nat.div_add_mod n chunks
    have h2 := Nat.mod_lt n hc
    have : chunks * sz = chunks * (n / chunks) + chunks := by rw [hsz]; ring
    rw [this]
    generalize chunks * (n / chunks) = A at h1 ⊢
    omega
  have hstep := h (i / sz) hj
  change allFrom p (i / sz * sz) sz = true at hstep
  have := (allFrom_iff p _ _).1 hstep (i % sz) (Nat.mod_lt _ hsz0)
  have e : i / sz * sz + i % sz = i := by
    rw [mul_comm]
    exact Nat.div_add_mod i sz
  rwa [e] at this

section Invariant

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def invSubgroup (Y : Set X) (hY : Y.Finite) : Subgroup G where
  carrier := {g | ∀ y ∈ Y, g • y ∈ Y}
  one_mem' := fun y hy => by simpa using hy
  mul_mem' := fun {a b} ha hb y hy => by
    rw [mul_smul]
    exact ha _ (hb y hy)
  inv_mem' := fun {g} hg y hy => by
    have hbij := (hY.injOn_iff_bijOn_of_mapsTo (f := fun x => g • x) hg).1
      (fun a _ b _ hab => smul_left_cancel g hab)
    obtain ⟨y', hy', hyy'⟩ := hbij.surjOn hy
    have : g⁻¹ • y = y' := by
      rw [← hyy']
      simp
    rw [this]
    exact hy'

theorem orbit_closure_subset {S : Set G} {Y : Set X} (hY : Y.Finite)
    (h : ∀ s ∈ S, ∀ y ∈ Y, s • y ∈ Y) {x : X} (hx : x ∈ Y) :
    MulAction.orbit (Subgroup.closure S) x ⊆ Y := by
  have hle : Subgroup.closure S ≤ invSubgroup Y hY :=
    (Subgroup.closure_le _).2 fun s hs => h s hs
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  exact hle hg x hx

theorem smul_mem_orbit_closure {S : Set G} {s : G} (hs : s ∈ S) {x y : X}
    (hy : y ∈ MulAction.orbit (Subgroup.closure S) x) :
    s • y ∈ MulAction.orbit (Subgroup.closure S) x :=
  MulAction.mem_orbit_of_mem_orbit (⟨s, Subgroup.subset_closure hs⟩ : Subgroup.closure S) hy

end Invariant

theorem actGo_lt (rows : Array ℕ) (v : ℕ) (hr : ∀ i < 24, rows[i]! < 2 ^ 24) :
    ∀ n acc, n ≤ 24 → acc < 2 ^ 24 → Native.actGo rows v n acc < 2 ^ 24
  | 0, acc, _, h => h
  | n + 1, acc, hn, h => by
    rw [Native.actGo]
    refine actGo_lt rows v hr n _ (by omega) ?_
    by_cases hb : v.testBit n = true
    · rw [ite_eq_left hb]
      exact Nat.xor_lt_two_pow h (hr n (by omega))
    · rw [ite_eq_right hb]
      exact h

theorem frameRows_lt : ∀ g < 15, ∀ i < 24, (frameRows[g]!)[i]! < 2 ^ 24 := by decide

theorem gimg_lt {g : ℕ} (hg : g < 15) (v : ℕ) : gimg g v < 2 ^ 24 :=
  actGo_lt _ v (frameRows_lt g hg) 24 0 le_rfl (by norm_num)

@[expose] def foundSet (T : FrameTables) : Finset ℕ :=
  (Finset.range (2 ^ 24)).filter fun v => rd8 T.klev v ≠ 0

@[expose] def labelSet (T : FrameTables) (o : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ 24)).filter fun v => rd8 T.klev v ≠ 0 ∧ rd8 T.olab v = o

structure FrameFacts (T : FrameTables) : Prop where
  point : ∀ v < 2 ^ 24, pointOK T v = true
  card_found : (foundSet T).card = deltaCount
  card_label : ∀ o, 1 ≤ o → o ≤ 6 → (labelSet T o).card = frameSizes[o - 1]!
  rep : ∀ o, 1 ≤ o → o ≤ 6 →
    frameReps[o - 1]! < 2 ^ 24 ∧ rd8 T.klev frameReps[o - 1]! ≠ 0 ∧ rd8 T.olab frameReps[o - 1]! = o


section Orbits

variable {G X : Type*} [Group G] [MulAction G X] {T : FrameTables} {dec : ℕ → X} {kGen : ℕ → G}

namespace FrameFacts


theorem injOn_dec (hdec : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b)
    (s : Finset ℕ) (hs : s ⊆ Finset.range (2 ^ 24)) : Set.InjOn dec (s : Set ℕ) :=
  fun a ha b hb hab => hdec a b (Finset.mem_range.1 (hs ha)) (Finset.mem_range.1 (hs hb)) hab


end FrameFacts

end Orbits

end CFSG.Monster.VisCert
