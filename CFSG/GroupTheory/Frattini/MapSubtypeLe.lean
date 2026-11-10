module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem frattini_map_subtype_le_of_commutator_le_of_pow_mem {p : ℕ} [Fact p.Prime]
    {V Z : Subgroup G} [Finite ↥V] (hV : IsPGroup p V) (hc : ⁅V, V⁆ ≤ Z)
    (hs : ∀ v ∈ V, v ^ p ∈ Z) : (frattini ↥V).map V.subtype ≤ Z := by
  haveI : Fact (IsPGroup p ↥V) := ⟨hV⟩
  rw [Subgroup.map_le_iff_le_comap,
    CFSG.frattini_eq_closure_commutator_union_powers (p := p), Subgroup.closure_le]
  rintro x (hx | ⟨y, rfl⟩)
  · have key : ∀ g h : ↥V, ⁅g, h⁆ ∈ Z.comap V.subtype := fun g h => by
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact hc (Subgroup.commutator_mem_commutator g.2 h.2)
    have hc' : (⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆) ≤ Z.comap V.subtype :=
      Subgroup.commutator_le.mpr (fun g _ h _ => key g h)
    exact hc' hx
  · rw [SetLike.mem_coe, Subgroup.mem_comap]
    simpa using hs y.1 y.2

section Finite

variable [Finite G]

theorem frattini_map_subtype_mono {A B : Subgroup G}
    (hB : IsPGroup 2 B) (hAB : A ≤ B) :
    (frattini ↥A).map A.subtype ≤ (frattini ↥B).map B.subtype := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥B) := ⟨hB⟩
  refine frattini_map_subtype_le_of_commutator_le_of_pow_mem
    (p := 2) (V := A) (Z := (frattini ↥B).map B.subtype) (hB.to_le hAB) ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    have hcommB : _root_.commutator ↥B ≤ frattini ↥B :=
      CFSG.commutator_le_frattini_of_isPGroup (R := ↥B) (p := 2)
    have hmem : ⁅(⟨x, hAB hx⟩ : B), (⟨y, hAB hy⟩ : B)⁆ ∈ frattini ↥B :=
      hcommB (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    exact Subgroup.mem_map.mpr ⟨_, hmem, map_commutatorElement B.subtype _ _⟩
  · intro x hx
    have hpow : (⟨x, hAB hx⟩ : B) ^ 2 ∈ frattini ↥B :=
      CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥B) (p := 2) _
    exact Subgroup.mem_map.mpr ⟨(⟨x, hAB hx⟩ : B) ^ 2, hpow, by simp⟩


end Finite

end CFSG.GroupTheory
