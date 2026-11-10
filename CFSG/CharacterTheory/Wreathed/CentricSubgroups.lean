module

public import CFSG.CharacterTheory.Wreathed.OriginalCoordinates

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

@[expose] def IsCentric {m : ℕ} (P : Subgroup (Wreath m)) : Prop :=
  Subgroup.centralizer (P : Set (Wreath m)) = (Subgroup.center P).map P.subtype

theorem center_le_of_centric {m : ℕ} (P : Subgroup (Wreath m)) (hP : IsCentric P) :
    Subgroup.center (Wreath m) ≤ P := by
  have hcenter := Subgroup.center_le_centralizer (P : Set (Wreath m))
  rw [hP] at hcenter
  exact hcenter.trans (Subgroup.map_subtype_le _)

theorem centric_eq_base_of_le {m : ℕ} (P : Subgroup (Wreath m))
    (hP : IsCentric P) (hbase : P ≤ baseSubgroup m) : P = baseSubgroup m := by
  apply le_antisymm hbase
  have hcentral : baseSubgroup m ≤ Subgroup.centralizer (P : Set (Wreath m)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hcomm := isMulCommutative_iff.mp (base_is_abelian m)
      (⟨p, hbase hp⟩ : baseSubgroup m) ⟨g, hg⟩
    exact congrArg Subtype.val hcomm
  rw [hP] at hcentral
  exact hcentral.trans (Subgroup.map_subtype_le _)


theorem abelian_centric_base_intersection (m : ℕ) (hm : 1 < m)
    (P : Subgroup (Wreath m)) (hP : IsCentric P) (habelian : IsMulCommutative P)
    (w : Wreath m) (hw : w ∈ P) (hout : w ∉ baseSubgroup m) :
    P ⊓ baseSubgroup m = Subgroup.center (Wreath m) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨c, d, f⟩, hcoord⟩ := (coordinateEquiv m).symm.surjective w
    change element m c d f = w at hcoord
    have hf : f = 1 := by
      rcases swap_exponent_cases f with h | h
      · exact False.elim (hout (by rw [← hcoord, element_mem_base, h]))
      · exact h
    rw [hf] at hcoord
    obtain ⟨⟨i, j, e⟩, hgcoord⟩ := (coordinateEquiv m).symm.surjective g
    change element m i j e = g at hgcoord
    have he : e = 0 := by
      have hbase := hg.2
      change g ∈ baseSubgroup m at hbase
      rw [← hgcoord, element_mem_base] at hbase
      exact hbase
    rw [he] at hgcoord
    have hcomm := isMulCommutative_iff.mp habelian (⟨g, hg.1⟩ : P) ⟨w, hw⟩
    have heq := congrArg Subtype.val hcomm
    change g * w = w * g at heq
    rw [← hcoord, ← hgcoord] at heq
    rw [← hgcoord, element_mem_center_iff m hm]
    exact ⟨rfl, (base_commutes_swap_iff m i j c d).mp heq⟩
  · intro g hg
    refine ⟨center_le_of_centric P hP hg, ?_⟩
    obtain ⟨⟨i, j, e⟩, hgcoord⟩ := (coordinateEquiv m).symm.surjective g
    change element m i j e = g at hgcoord
    rw [← hgcoord, element_mem_center_iff m hm] at hg
    change g ∈ baseSubgroup m
    rw [← hgcoord, element_mem_base]
    exact hg.1

theorem subgroup_outside_exists (m : ℕ) (P : Subgroup (Wreath m))
    (hout : ¬ P ≤ baseSubgroup m) : ∃ i j : ZMod m, element m i j 1 ∈ P := by
  by_contra h
  apply hout
  intro g hg
  obtain ⟨⟨i, j, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
  change element m i j e ∈ P at hg
  change element m i j e ∈ baseSubgroup m
  rcases swap_exponent_cases e with rfl | rfl
  · simp
  · exact False.elim (h ⟨i, j, hg⟩)

theorem subgroup_base_cosets (m : ℕ) (P : Subgroup (Wreath m))
    (i j : ZMod m) (hw : element m i j 1 ∈ P) (g : Wreath m) :
    g ∈ P ↔ g ∈ P ⊓ baseSubgroup m ∨
      ∃ b ∈ P ⊓ baseSubgroup m, g = b * element m i j 1 := by
  constructor
  · intro hg
    obtain ⟨⟨c, d, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
    change element m c d e ∈ P at hg
    change element m c d e ∈ P ⊓ baseSubgroup m ∨
      ∃ b ∈ P ⊓ baseSubgroup m, element m c d e = b * element m i j 1
    rcases swap_exponent_cases e with rfl | rfl
    · exact Or.inl ⟨hg, by simp⟩
    · refine Or.inr ⟨element m c d 1 * (element m i j 1)⁻¹,
        ⟨P.mul_mem hg (P.inv_mem hw), ?_⟩, ?_⟩
      · rw [element_swap_inv, element_swap_mul, show (1 + 1 : ZMod 2) = 0 by decide]
        simp
      · group
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact h.1
    · exact P.mul_mem hb.1 hw


end CFSG.Wreathed
