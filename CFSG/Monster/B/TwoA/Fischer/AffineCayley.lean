module

public import CFSG.Monster.B.TwoA.Fischer.AffineCayleyGraph

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

omit hS in
theorem ncard_inter_biUnion_hexadFiber {C : Set V}
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    (h77 : (cliqueBlocks lab C).ncard = 77) {P : Set V} (hP : P.Finite) {c : ℕ}
    (hc : ∀ B ∈ cliqueBlocks lab C, (P ∩ hexadFiber lab Y C B).ncard = c) :
    (P ∩ ⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B).ncard = 77 * c := by
  classical
  set Q := P ∩ ⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B with hQdef
  have hQfin : Q.Finite := hP.subset Set.inter_subset_left
  have hℬfin : (cliqueBlocks lab C).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [h77]; norm_num)
  have hmaps : Set.MapsTo (fun x => C ∩ (sliceGraph lab Y).neighborSet x) hQfin.toFinset
      hℬfin.toFinset := by
    intro x hx
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hx ⊢
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 hx.2
    change C ∩ (sliceGraph lab Y).neighborSet x ∈ cliqueBlocks lab C
    rw [hxB.2.2]
    exact hB
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ B ∈ hℬfin.toFinset,
      {x ∈ hQfin.toFinset | C ∩ (sliceGraph lab Y).neighborSet x = B}.card = c := by
    intro B hB
    rw [Set.Finite.mem_toFinset] at hB
    rw [← hc B hB, ← Set.ncard_coe_finset]
    congr 1
    ext x
    rw [Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨hxP, hxU⟩, hxB⟩
      obtain ⟨B', -, hxB'⟩ := Set.mem_iUnion₂.1 hxU
      exact ⟨hxP, hxB'.1, hxB'.2.1, hxB⟩
    · rintro ⟨hxP, hx⟩
      exact ⟨⟨hxP, Set.mem_iUnion₂.2 ⟨B, hB, hx⟩⟩, hx.2.2⟩
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ hℬfin, h77] at h
  rw [Set.ncard_eq_toFinset_card _ hQfin, h]

section Max

variable {C : Set V} (hC : IsSliceMaxClique lab Y C)
  [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
include hC

theorem neighborSet_inter_omega_eq {x : V} (hx : x ∈ hexadFiber lab Y C ∅) :
    (sliceGraph lab Y).neighborSet x ∩ hexadFiber lab Y C ∅ =
      (fun r => act r x) '' labelLayer lab C 2 := by
  ext y
  constructor
  · rintro ⟨hxy, hy⟩
    obtain ⟨r, ⟨hr, rfl⟩, -⟩ := hS.existsUnique_act_eq hC hx hy
    exact ⟨r, (hS.adj_iff_mem_labelLayer_two hC hx hr).1 hxy, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    have hrR := hS.labelLayer_subset hC 2 hr
    exact ⟨(hS.adj_iff_mem_labelLayer_two hC hx hrR).2 hr, hS.act_mem_hexadFiber hrR hx⟩

theorem ncard_image_labelLayer {x : V} (hx : x ∈ hexadFiber lab Y C ∅) (i : ℕ) :
    ((fun r => act r x) '' labelLayer lab C i).ncard = (labelLayer lab C i).ncard :=
  Set.InjOn.ncard_image ((hS.act_injOn hC hx).mono (hS.labelLayer_subset hC i))

theorem exists_fix_image_block {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {B B' : Set V}
    (hB : B ∈ cliqueBlocks lab C) (hB' : B' ∈ cliqueBlocks lab C) :
    ∃ k ∈ setStab act lab Y C ⊓ actStab act x, act k '' B = B' := by
  obtain ⟨_, -, -, -, -, -, hB6, hSt, -⟩ := hS.clique_code_steiner_design hC
  obtain ⟨T, hTB, hT3⟩ := Set.exists_subset_card_eq (s := B) (n := 3)
    (by rw [(hB6 B hB).2]; norm_num)
  obtain ⟨T', hT'B', hT'3⟩ := Set.exists_subset_card_eq (s := B') (n := 3)
    (by rw [(hB6 B' hB').2]; norm_num)
  obtain ⟨k, hk, hkT⟩ := hS.exists_fix_image_eq hC hx (hTB.trans (hB6 B hB).1)
    (hT'B'.trans (hB6 B' hB').1) (by rw [hT3, hT'3]) (by rw [hT3])
  refine ⟨k, hk, ?_⟩
  have hkB : act k '' B ∈ cliqueBlocks lab C :=
    image_mem_cliqueBlocks hS.lab_act (fun z hz => (hk.1.2 z).2 hz)
      (setStabPerm act lab Y C ⟨k, hk.1⟩) (fun _ => rfl) hB
  obtain ⟨B₀, -, huniq⟩ := hSt T' (hT'B'.trans (hB6 B' hB').1) hT'3
  rw [huniq _ ⟨hkB, by rw [← hkT]; exact Set.image_mono hTB⟩, huniq B' ⟨hB', hT'B'⟩]

theorem ncard_neighborSet_inter_hexadFiber {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {B : Set V}
    (hB : B ∈ cliqueBlocks lab C) :
    ((sliceGraph lab Y).neighborSet x ∩ hexadFiber lab Y C B).ncard = 6 := by
  obtain ⟨_, -, -, hcov, -, -, hdUΩ, -, -, -, -, -, -⟩ := hS.clique_hexad_fibers hC
  obtain ⟨_, -, -, -, -, -, -, -, h77, -⟩ := hS.clique_code_steiner_design hC
  set N := (sliceGraph lab Y).neighborSet x with hN
  have hNfin : N.Finite := hS.finite.subset fun _ h => h.2.1
  have hconst : ∀ B' ∈ cliqueBlocks lab C,
      (N ∩ hexadFiber lab Y C B').ncard = (N ∩ hexadFiber lab Y C B).ncard := by
    intro B' hB'
    obtain ⟨k, hk, hkB⟩ := hS.exists_fix_image_block hC hx hB hB'
    have hkx : act k x = x := hk.2
    have e : act k '' (N ∩ hexadFiber lab Y C B) = N ∩ hexadFiber lab Y C B' := by
      rw [Set.image_inter (act k).injective, hN, hS.image_neighborSet hk.1.1, hkx,
        hS.image_hexadFiber hk.1 B, hkB]
    rw [← e, Set.ncard_image_of_injective _ (act k).injective]
  have hU := ncard_inter_biUnion_hexadFiber (Y := Y) h77 hNfin hconst
  have hNC : ∀ y ∈ N, y ∉ C := fun y hy hyC => by
    have h : y ∈ C ∩ (sliceGraph lab Y).neighborSet x := ⟨hyC, hy⟩
    rw [hx.2.2] at h
    exact h
  have hsplit : N = (N ∩ ⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B) ∪
      (N ∩ hexadFiber lab Y C ∅) := by
    ext y
    constructor
    · intro hy
      have hyY : y ∈ Y := hy.2.1
      rw [hcov] at hyY
      rcases hyY with (h | h) | h
      · exact absurd h (hNC y hy)
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have h693 := hS.valency x hx.1
  rw [← hN, hsplit, Set.ncard_union_eq
    (Disjoint.mono Set.inter_subset_right Set.inter_subset_right hdUΩ)
    (hNfin.subset Set.inter_subset_left) (hNfin.subset Set.inter_subset_left), hU,
    hS.neighborSet_inter_omega_eq hC hx, hS.ncard_image_labelLayer hC hx,
    hS.ncard_labelLayer_two hC] at h693
  omega


end Max


end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
