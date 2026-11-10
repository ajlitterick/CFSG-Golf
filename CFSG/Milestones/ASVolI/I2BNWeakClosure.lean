module

public import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.ASVolI

open CFSG.Open

section burnsideI25bBN

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem
open scoped Pointwise

variable {G : Type} [Group G] {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}


theorem burnsideI25b_mem_parabolic_single_iff (h : IsBNPair B N S) {s : WeylGroup B N}
    (hs : s ∈ S) {x : G} : x ∈ parabolic B N {s} ↔ x ∈ B ∨ x ∈ dc B N s := by
  have hJ : ({s} : Set (WeylGroup B N)) ⊆ S := Set.singleton_subset_iff.2 hs
  rw [h.mem_parabolic_iff hJ]
  constructor
  · rintro ⟨w, hw, hx⟩
    rcases eq_one_or_eq_of_mem_closure_singleton (h.mul_self_eq_one hs) hw with rfl | rfl
    · left; exact mem_dc_one.1 hx
    · right; exact hx
  · rintro (hx | hx)
    · exact ⟨1, Subgroup.one_mem _, mem_dc_one.2 hx⟩
    · exact ⟨s, Subgroup.subset_closure rfl, hx⟩


theorem burnsideI25b_length_lt_mul_right (h : IsBNPair B N S) {J : Set (WeylGroup B N)}
    (hJ : J ⊆ S) {w s : WeylGroup B N} (hw : w ∈ Subgroup.closure J) (hs : s ∈ S) (hsJ : s ∉ J) :
    wordLength S w < wordLength S (w * s) := by
  by_contra hcon
  push Not at hcon
  have hinv : wordLength S (s * w⁻¹) = wordLength S (w * s) := by
    have := h.length_inv (w * s)
    rw [mul_inv_rev, h.inv_eq_self hs] at this
    exact this
  have hor := h.length_mul_eq_or hs w⁻¹
  have hlinv : wordLength S w⁻¹ = wordLength S w := h.length_inv w
  have hne := h.length_mul_ne hs w⁻¹
  have hlt : wordLength S (s * w⁻¹) + 1 = wordLength S w⁻¹ := by omega
  have hwinv : w⁻¹ ∈ Subgroup.closure J := Subgroup.inv_mem _ hw
  obtain ⟨ns, hns⟩ := QuotientGroup.mk_surjective s
  have hdc : ∀ x ∈ dc B N s, x ∈ parabolic B N J := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := h.bnCore.dc_subset_mul_inv hs (h.mem_closure w⁻¹) hlt x hx
    exact (parabolic B N J).mul_mem (h.dc_subset_parabolic hJ hwinv ha)
      ((parabolic B N J).inv_mem (h.dc_subset_parabolic hJ hwinv hb))
  have hnsP : (ns : G) ∈ parabolic B N J := hdc _ (hns ▸ coe_mem_dc ns)
  have hsJ' : s ∈ Subgroup.closure J :=
    (h.mem_parabolic_iff_of_mem_dc hJ (hns ▸ coe_mem_dc ns)).1 hnsP
  exact hsJ (h.mem_of_mem_closure hJ hs hsJ')

theorem burnsideI25b_exists_max [Finite G] (S J : Set (WeylGroup B N)) :
    ∃ n : N, (n : WeylGroup B N) ∈ Subgroup.closure J ∧
      ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S (n : WeylGroup B N) := by
  have hfin : (Subgroup.closure J : Set (WeylGroup B N)).Finite := Set.toFinite _
  obtain ⟨w₀, hw₀, hmax⟩ := Set.exists_max_image (Subgroup.closure J : Set (WeylGroup B N))
    (wordLength S) hfin ⟨1, Subgroup.one_mem _⟩
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w₀
  exact ⟨n, hw₀, fun w hw => hmax w hw⟩

theorem burnsideI25b_conj_mem_H {c x : G} (hc : c ∈ B ⊓ N) (hx : x ∈ N) :
    x * c * x⁻¹ ∈ B ⊓ N := by
  have hmem : (⟨c, (Subgroup.mem_inf.1 hc).2⟩ : N) ∈ (B ⊓ N).subgroupOf N :=
    Subgroup.mem_subgroupOf.2 hc
  have := (inferInstance : ((B ⊓ N).subgroupOf N).Normal).conj_mem _ hmem ⟨x, hx⟩
  exact Subgroup.mem_subgroupOf.1 this


end burnsideI25bBN

section burnsideI25bPCore

variable {G : Type} [Group G]


end burnsideI25bPCore

section burnsideI25bMain

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem
open scoped Pointwise

variable {G : Type} [Group G] {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}


end burnsideI25bMain

section burnsideI25bWrap

open scoped Pointwise

variable {G : Type} [Group G]


end burnsideI25bWrap

section burnsideI25cWeyl

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem

variable {G : Type} [Group G] {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}

theorem burnsideI25c_cslength_eq (h : IsBNPair B N S)
    (cs : CoxeterSystem (orderMatrix h.orderOf_eq_two) (WeylGroup B N))
    (hcs : ∀ s : S, cs.simple s = s) (w : WeylGroup B N) :
    cs.length w = wordLength S w := by
  apply le_antisymm
  · obtain ⟨l, hl, hlen, hprod⟩ :=
      exists_list_length_eq_wordLength h.bnCore.mul_self_eq_one (h.mem_closure w)
    let ω : List S := l.pmap Subtype.mk hl
    have hω : cs.wordProd ω = w := by
      unfold CoxeterSystem.wordProd
      rw [List.map_congr_left (fun s _ => hcs s)]
      rw [List.map_pmap, List.pmap_eq_map, List.map_id', hprod]
    calc cs.length w = cs.length (cs.wordProd ω) := by rw [hω]
      _ ≤ ω.length := cs.length_wordProd_le ω
      _ = l.length := List.length_pmap
      _ = wordLength S w := hlen
  · obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    have hl : ∀ s ∈ ω.map Subtype.val, s ∈ S := by
      intro s hs
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hs
      exact y.2
    have hprod : (ω.map Subtype.val).prod = cs.wordProd ω := by
      unfold CoxeterSystem.wordProd
      rw [List.map_congr_left (fun s _ => hcs s)]
    have := wordLength_le (J := S) hl
    rw [hprod, List.length_map] at this
    rw [hω.eq]
    exact this


theorem burnsideI25c_prefix_longest (h : IsBNPair B N S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    {w₀ : WeylGroup B N} (hw₀ : w₀ ∈ Subgroup.closure J)
    (hmax : ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S w₀)
    {x : WeylGroup B N} (hx : x ∈ Subgroup.closure J) :
    wordLength S x + wordLength S (x⁻¹ * w₀) = wordLength S w₀ := by
  obtain ⟨cs, hcs⟩ := h.exists_coxeterSystem
  have hl := burnsideI25c_cslength_eq h cs hcs
  suffices key : ∀ k : ℕ, ∀ x ∈ Subgroup.closure J, wordLength S x = k →
      wordLength S x + wordLength S (x⁻¹ * w₀) = wordLength S w₀ from key _ x hx rfl
  intro k
  induction k with
  | zero =>
    intro x hx hxk
    have : x = 1 :=
      (wordLength_eq_zero_iff h.bnCore.mul_self_eq_one (h.mem_closure x)).1 hxk
    subst this
    simp [wordLength_one]
  | succ k ih =>
    intro x hx hxk
    have hx1 : x ≠ 1 := by
      intro h1
      rw [h1, wordLength_one] at hxk
      omega
    obtain ⟨r, hrS, hdesc⟩ :=
      exists_right_descent h.bnCore.mul_self_eq_one (h.mem_closure x) hx1
    have hrJ : r ∈ J := by
      by_contra hrJ
      have := burnsideI25b_length_lt_mul_right h hJ hx hrS hrJ
      omega
    have hrr : r * r = 1 := h.mul_self_eq_one hrS
    set x' := x * r with hx'
    have hx'J : x' ∈ Subgroup.closure J :=
      Subgroup.mul_mem _ hx (Subgroup.subset_closure hrJ)
    have hxx' : x = x' * r := by rw [hx', mul_assoc, hrr, mul_one]
    have hlx' : wordLength S x' = k := by omega
    have IH := ih x' hx'J hlx'
    set v' := x'⁻¹ * w₀ with hv'
    have hw₀eq : x' * v' = w₀ := by rw [hv']; group
    obtain ⟨ω', hω', hω'prod⟩ := cs.exists_isReduced x'
    obtain ⟨ω'', hω'', hω''prod⟩ := cs.exists_isReduced v'
    have hlen' : ω'.length = wordLength S x' := by rw [← hl, ← hω'.eq, ← hω'prod]
    have hlen'' : ω''.length = wordLength S v' := by rw [← hl, ← hω''.eq, ← hω''prod]
    set ω := ω' ++ ω'' with hω
    have hπω : cs.wordProd ω = w₀ := by
      rw [hω, cs.wordProd_append, ← hω'prod, ← hω''prod, hw₀eq]
    set t : WeylGroup B N := x' * r * x'⁻¹ with ht
    have htref : cs.IsReflection t := by
      refine ⟨x', ⟨r, hrS⟩, ?_⟩
      rw [hcs ⟨r, hrS⟩]
    have htw₀ : t * w₀ = x' * (r * v') := by
      rw [ht, ← hw₀eq]; group
    have htinJ : t * w₀ ∈ Subgroup.closure J := by
      rw [htw₀]
      refine Subgroup.mul_mem _ hx'J (Subgroup.mul_mem _ (Subgroup.subset_closure hrJ) ?_)
      rw [hv']
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx'J) hw₀
    have hlt : cs.length (t * w₀) < cs.length w₀ := by
      rw [hl, hl]
      have h1 := hmax _ htinJ
      have h2 : cs.length (t * w₀) ≠ cs.length w₀ := htref.length_mul_right_ne w₀
      rw [hl, hl] at h2
      omega
    have hinv : cs.IsLeftInversion (cs.wordProd ω) t := by
      rw [hπω]
      exact ⟨htref, hlt⟩
    obtain ⟨j, hj, hjeq⟩ := CoxeterSystem.strongExchange cs hinv
    rw [hπω] at hjeq
    have hxinv : x⁻¹ * w₀ = r * v' := by
      rw [hxx', mul_inv_rev, h.inv_eq_self hrS, hv', mul_assoc]
    by_cases hjlt : j < ω'.length
    · exfalso
      rw [hω, List.eraseIdx_append_of_lt_length hjlt, cs.wordProd_append, ← hω''prod] at hjeq
      have h1 : t * x' * v' = cs.wordProd (ω'.eraseIdx j) * v' := by
        rw [mul_assoc, hw₀eq]; exact hjeq
      have h2 := mul_right_cancel h1
      have hX : x = cs.wordProd (ω'.eraseIdx j) := by
        calc x = x' * r := hxx'
          _ = t * x' := by rw [ht]; group
          _ = _ := h2
      have h3 := cs.length_wordProd_le (ω'.eraseIdx j)
      rw [← hX, List.length_eraseIdx_of_lt hjlt] at h3
      have h4 : cs.length x = wordLength S x := hl x
      omega
    · have hjge : ω'.length ≤ j := not_lt.1 hjlt
      rw [hω, List.eraseIdx_append_of_length_le hjge, cs.wordProd_append, ← hω'prod] at hjeq
      have h2 : r * v' = cs.wordProd (ω''.eraseIdx (j - ω'.length)) := by
        have : x' * (r * v') = x' * cs.wordProd (ω''.eraseIdx (j - ω'.length)) := by
          rw [← htw₀]; exact hjeq
        exact mul_left_cancel this
      have hj'' : j - ω'.length < ω''.length := by
        have := hj
        rw [hω, List.length_append] at this
        omega
      have h3 := cs.length_wordProd_le (ω''.eraseIdx (j - ω'.length))
      rw [← h2, List.length_eraseIdx_of_lt hj''] at h3
      have h5 : wordLength S (x⁻¹ * w₀) ≤ wordLength S v' - 1 := by
        rw [hxinv, ← hl]
        rw [hlen''] at h3
        exact h3
      have h6 : wordLength S w₀ ≤ wordLength S x + wordLength S (x⁻¹ * w₀) := by
        have := wordLength_mul_le h.bnCore.mul_self_eq_one (h.mem_closure x)
          (h.mem_closure (x⁻¹ * w₀))
        rwa [mul_inv_cancel_left] at this
      omega

end burnsideI25cWeyl

section burnsideI25cSetup

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem


end burnsideI25cSetup

section burnsideI25cGroup

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem


end burnsideI25cGroup

section burnsideI25cMain

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem


end burnsideI25cMain

section burnsideI25cStar

open CFSG.ASVolI.ChIJK CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem
open scoped Pointwise


end burnsideI25cStar

end CFSG.ASVolI
