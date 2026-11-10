module

public import CFSG.Sporadic.Schreier.ONCompactSpec
public import CFSG.Sporadic.Th.OrbitSpec

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native

variable {n : ℕ} {root : ℕ} {steps : Array (Array ℕ)} {L : CLevel}
  {gens : List (Equiv.Perm (Fin n))}

theorem getD_mem_list {α : Type*} {l : List α} {j : ℕ} (hj : j < l.length) (d : α) :
    l.getD j d ∈ l := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj


theorem tree_mem_orbit (hL : CLevelFacts n root steps L)
    (hS : ∀ j < steps.size, PRep n steps[j]! (gens.getD j 1)) (hlen : steps.size = gens.length)
    (hr : root < n) :
    ∀ k < L.pts.size, ∃ g ∈ Subgroup.closure {g | g ∈ gens},
      ((g ⟨root, hr⟩ : Fin n) : ℕ) = L.pts[k]! := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0
      exact ⟨1, one_mem _, by rw [hL.root]; rfl⟩
    · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hp := hL.par_lt k hk hpos
      obtain ⟨g, hg, hgr⟩ := ih _ hp (by omega)
      have hl := hL.lab_lt k hk hpos
      refine ⟨gens.getD (L.lab[k]!) 1 * g, mul_mem (Subgroup.subset_closure ?_) hg, ?_⟩
      · exact getD_mem_list (by rw [← hlen]; exact hl) 1
      · rw [Equiv.Perm.mul_apply, ← hS _ hl (g ⟨root, hr⟩), hgr, hL.edge k hk hpos]

theorem tree_closed (hL : CLevelFacts n root steps L)
    (hS : ∀ j < steps.size, PRep n steps[j]! (gens.getD j 1)) {z : Fin n}
    (hz : L.pos[(z : ℕ)]! < L.pts.size) {j : ℕ} (hj : j < steps.size) :
    L.pos[((gens.getD j 1 z : Fin n) : ℕ)]! < L.pts.size := by
  have h := (hL.closed _ hz j hj).1
  rw [hL.pts_pos z z.isLt hz, hS j hj z] at h
  exact h

theorem mem_orbit_iff_tree (hL : CLevelFacts n root steps L)
    (hS : ∀ j < steps.size, PRep n steps[j]! (gens.getD j 1)) (hlen : steps.size = gens.length)
    (hr : root < n) (z : Fin n) :
    z ∈ MulAction.orbit (Subgroup.closure {g | g ∈ gens}) (⟨root, hr⟩ : Fin n) ↔
      L.pos[(z : ℕ)]! < L.pts.size := by
  set K := Subgroup.closure {g | g ∈ gens}
  set T : Set (Fin n) := {y | L.pos[(y : ℕ)]! < L.pts.size}
  have hinv : ∀ g ∈ K, ∀ y ∈ T, g y ∈ T := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      intro y hy
      have e : gens[j] = gens.getD j 1 := (List.getD_eq_getElem _ _ hj).symm
      rw [e]
      exact tree_closed hL hS hy (by rw [hlen]; exact hj)
    | one => exact fun y hy => hy
    | mul g h _ _ hg hh => exact fun y hy => hg _ (hh y hy)
    | inv g _ hg =>
      exact CFSG.Sporadic.Th.inv_smul_mem_of_subset_of_finite (G := Equiv.Perm (Fin n))
        (Set.toFinite T) hg
  have hroot : (⟨root, hr⟩ : Fin n) ∈ T := by
    show L.pos[root]! < L.pts.size
    have := hL.pos_pts 0 hL.pos
    rw [hL.root] at this
    rw [this]
    exact hL.pos
  constructor
  · rintro ⟨g, rfl⟩
    exact hinv g g.2 _ hroot
  · intro hz
    obtain ⟨g, hg, hgr⟩ := tree_mem_orbit hL hS hlen hr _ hz
    refine ⟨⟨g, hg⟩, Fin.ext ?_⟩
    show ((g ⟨root, hr⟩ : Fin n) : ℕ) = z
    rw [hgr, hL.pts_pos z z.isLt hz]


end CFSG.Sporadic.ONOddCore
