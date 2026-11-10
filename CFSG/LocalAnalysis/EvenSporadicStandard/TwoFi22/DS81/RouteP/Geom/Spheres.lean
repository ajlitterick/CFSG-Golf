module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Dist

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native

section Spheres


theorem orbLabel_eq_iff (i : Fin 7) (v : Ω) :
    orbLabel v = i.val ↔ v ∈ MulAction.orbit Zp (repPt i) := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := exists_mem_orbit_repPt v
    have h' : orbLabel v = j.val := by
      rw [orbLabel_eq_of_mem_orbit hj, orbLabel_repPt]
    have : j = i := Fin.ext (h'.symm.trans h)
    exact this ▸ hj
  · intro h
    rw [orbLabel_eq_of_mem_orbit h, orbLabel_repPt]

theorem distLevel_eq_iff (n : ℕ) (v : Ω) :
    distLevel v = n ↔
      ∃ i : Fin 7, geomLevels[i.val]! = n ∧ v ∈ MulAction.orbit Zp (repPt i) := by
  constructor
  · intro h
    refine ⟨⟨orbLabel v, orbLabel_lt v⟩, h, ?_⟩
    exact (orbLabel_eq_iff ⟨orbLabel v, orbLabel_lt v⟩ v).1 rfl
  · rintro ⟨i, hi, hv⟩
    rw [distLevel_eq_of_mem_orbit hv, distLevel_repPt, hi]

theorem eq_of_mem_orbit_repPt_of_size_one {i : Fin 7} (hi : geomSizes[i.val]! = 1) {v : Ω}
    (hv : v ∈ MulAction.orbit Zp (repPt i)) : v = repPt i := by
  have h1 := card_orbit_repPt i
  rw [hi, Nat.card_eq_one_iff_unique] at h1
  obtain ⟨h1, -⟩ := h1
  exact congrArg Subtype.val (h1.elim ⟨v, hv⟩ ⟨repPt i, MulAction.mem_orbit_self _⟩)

theorem dist_x0_eq_zero_iff (v : Ω) : Δ.dist x0 v = 0 ↔ v = x0 := by
  rw [(Δ_reachable_x0 v).dist_eq_zero_iff]
  exact eq_comm


theorem dist_x0_eq_two_iff (v : Ω) : Δ.dist x0 v = 2 ↔ v ∈ MulAction.orbit Zp y2 := by
  rw [Δ_dist_x0, distLevel_eq_iff]
  have key : ∀ i : Fin 7, geomLevels[i.val]! = 2 → i = 2 := by decide
  constructor
  · rintro ⟨i, hi, hv⟩
    obtain rfl := key i hi
    exact hv
  · intro hv
    exact ⟨2, by decide, hv⟩

theorem dist_x0_eq_three_iff (v : Ω) :
    Δ.dist x0 v = 3 ↔ v ∈ MulAction.orbit Zp y3a ∨ v ∈ MulAction.orbit Zp y3b := by
  rw [Δ_dist_x0, distLevel_eq_iff]
  have key : ∀ i : Fin 7, geomLevels[i.val]! = 3 → i = 3 ∨ i = 4 := by decide
  constructor
  · rintro ⟨i, hi, hv⟩
    rcases key i hi with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr hv
  · rintro (hv | hv)
    · exact ⟨3, by decide, hv⟩
    · exact ⟨4, by decide, hv⟩

theorem eq_y4a_of_mem_orbit {v : Ω} (hv : v ∈ MulAction.orbit Zp y4a) : v = y4a :=
  eq_of_mem_orbit_repPt_of_size_one (i := 5) (by decide) hv

theorem eq_y4b_of_mem_orbit {v : Ω} (hv : v ∈ MulAction.orbit Zp y4b) : v = y4b :=
  eq_of_mem_orbit_repPt_of_size_one (i := 6) (by decide) hv

theorem dist_x0_eq_four_iff (v : Ω) : Δ.dist x0 v = 4 ↔ v = y4a ∨ v = y4b := by
  rw [Δ_dist_x0, distLevel_eq_iff]
  have key : ∀ i : Fin 7, geomLevels[i.val]! = 4 → i = 5 ∨ i = 6 := by decide
  constructor
  · rintro ⟨i, hi, hv⟩
    rcases key i hi with rfl | rfl
    · exact Or.inl (eq_y4a_of_mem_orbit hv)
    · exact Or.inr (eq_y4b_of_mem_orbit hv)
  · rintro (rfl | rfl)
    · exact ⟨5, by decide, MulAction.mem_orbit_self _⟩
    · exact ⟨6, by decide, MulAction.mem_orbit_self _⟩


theorem exists_mem_repsDist_two {b : Ω} (hb : Δ.dist x0 b = 2) :
    ∃ r ∈ [y2], ∃ k ∈ Zp, k • r = b := by
  obtain ⟨⟨k, hk⟩, hkb⟩ := (dist_x0_eq_two_iff b).1 hb
  exact ⟨y2, List.mem_singleton_self _, k, hk, hkb⟩

theorem exists_mem_repsDist_three {b : Ω} (hb : Δ.dist x0 b = 3) :
    ∃ r ∈ [y3a, y3b], ∃ k ∈ Zp, k • r = b := by
  rcases (dist_x0_eq_three_iff b).1 hb with ⟨⟨k, hk⟩, hkb⟩ | ⟨⟨k, hk⟩, hkb⟩
  · exact ⟨y3a, by simp, k, hk, hkb⟩
  · exact ⟨y3b, by simp, k, hk, hkb⟩

theorem exists_mem_repsDist_four {b : Ω} (hb : Δ.dist x0 b = 4) :
    ∃ r ∈ [y4a, y4b], ∃ k ∈ Zp, k • r = b := by
  rcases (dist_x0_eq_four_iff b).1 hb with rfl | rfl
  · exact ⟨y4a, by simp, 1, Subgroup.one_mem _, one_smul _ _⟩
  · exact ⟨y4b, by simp, 1, Subgroup.one_mem _, one_smul _ _⟩


end Spheres

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
